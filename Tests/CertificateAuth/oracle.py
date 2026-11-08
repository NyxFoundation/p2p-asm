"""Independent cryptography/OpenSSL oracle. ALL fixed key seeds are TEST ONLY."""
import datetime
import hashlib
import struct
from dataclasses import dataclass
from cryptography import x509
from cryptography.hazmat.primitives import hashes, serialization
from cryptography.hazmat.primitives.asymmetric import ed25519, ec, rsa, padding, utils
from cryptography.x509.oid import NameOID, ExtendedKeyUsageOID, ObjectIdentifier

PREFIX = b'libp2p-tls-handshake:'
OID = ObjectIdentifier('1.3.6.1.4.1.53594.1.1')
K256_ORDER = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141


def test_seed(label):
    return hashlib.sha256(b'CERTIFICATE-AUTH-TEST-ONLY:' + label.encode()).digest()


def tlv(tag, payload):
    size = len(payload)
    if size < 128:
        length = bytes([size])
    else:
        raw = size.to_bytes((size.bit_length() + 7) // 8, 'big')
        length = bytes([128 + len(raw)]) + raw
    return bytes([tag]) + length + payload


@dataclass(frozen=True)
class Node:
    tag: int
    start: int
    body: int
    end: int

    def children(self, raw):
        result, cursor = [], self.body
        while cursor < self.end:
            node = parse(raw, cursor)
            result.append(node)
            cursor = node.end
        assert cursor == self.end
        return result

    @property
    def span(self):
        return self.start, self.end - self.start

    @property
    def content(self):
        return self.body, self.end - self.body


def parse(raw, start=0):
    first = raw[start + 1]
    if first < 128:
        body, size = start + 2, first
    else:
        count = first & 127
        body = start + 2 + count
        size = int.from_bytes(raw[start + 2:body], 'big')
    assert body + size <= len(raw)
    return Node(raw[start], start, body, body + size)


def public_bytes(key):
    if isinstance(key, ed25519.Ed25519PrivateKey):
        return key.public_key().public_bytes_raw()
    return key.public_key().public_bytes(serialization.Encoding.X962,
                                         serialization.PublicFormat.CompressedPoint)


def host_key(kind, seed):
    if kind == 1:
        return ed25519.Ed25519PrivateKey.from_private_bytes(seed)
    return ec.derive_private_key(int.from_bytes(seed, 'big'), ec.SECP256K1())


def host_signature(key, message):
    if isinstance(key, ed25519.Ed25519PrivateKey):
        return key.sign(message)
    encoded = key.sign(message, ec.ECDSA(hashes.SHA256(), deterministic_signing=True))
    r, s = utils.decode_dss_signature(encoded)
    return utils.encode_dss_signature(r, min(s, K256_ORDER - s))


def cv_message(role, digest):
    assert role in (1, 2) and len(digest) == 32
    role_name = b'server' if role == 1 else b'client'
    return b' ' * 64 + b'TLS 1.3, ' + role_name + b' CertificateVerify\0' + digest


def cv_signature(key, role, digest):
    message = cv_message(role, digest)
    if isinstance(key, ed25519.Ed25519PrivateKey):
        return key.sign(message)
    if isinstance(key, ec.EllipticCurvePrivateKey):
        return key.sign(message, ec.ECDSA(hashes.SHA256(), deterministic_signing=True))
    return key.sign(message, padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32),
                    hashes.SHA256())


def certificate(host_kind=1, subject_kind=1, pss=False, before=1700000000,
                after=1900000000, host_proto=None, eku=(1, 2), subject=None,
                host_sig=None, extra=()):
    """Generate with independent x509 builder and OpenSSL-backed real signing."""
    host_seed, seed = test_seed(f'host-{host_kind}'), test_seed('ephemeral')
    host = host_key(host_kind, host_seed)
    if subject is None:
        if subject_kind == 1:
            subject = ed25519.Ed25519PrivateKey.from_private_bytes(seed)
        elif subject_kind == 2:
            subject = ec.derive_private_key(int.from_bytes(seed, 'big'), ec.SECP256R1())
        else:
            subject = rsa.generate_private_key(public_exponent=65537, key_size=2048)
    spki = subject.public_key().public_bytes(serialization.Encoding.DER,
                                            serialization.PublicFormat.SubjectPublicKeyInfo)
    host_raw = public_bytes(host)
    protobuf = bytes([8, host_kind, 18, len(host_raw)]) + host_raw
    extension_proto = protobuf if host_proto is None else host_proto
    signature = host_signature(host, PREFIX + spki) if host_sig is None else host_sig
    signed = tlv(48, tlv(4, extension_proto) + tlv(4, signature))
    name = x509.Name([x509.NameAttribute(NameOID.COMMON_NAME, 'libp2p')])
    builder = (x509.CertificateBuilder().subject_name(name).issuer_name(name)
               .serial_number(1).public_key(subject.public_key())
               .not_valid_before(datetime.datetime.fromtimestamp(before, datetime.timezone.utc))
               .not_valid_after(datetime.datetime.fromtimestamp(after, datetime.timezone.utc))
               .add_extension(x509.UnrecognizedExtension(OID, signed), critical=True)
               .add_extension(x509.KeyUsage(True, False, False, False, False,
                                            False, False, None, None), critical=True))
    if eku is not None:
        values = {1: ExtendedKeyUsageOID.SERVER_AUTH, 2: ExtendedKeyUsageOID.CLIENT_AUTH}
        builder = builder.add_extension(x509.ExtendedKeyUsage([values[i] for i in eku]), False)
    for value, critical in extra:
        builder = builder.add_extension(value, critical)
    options = {'ecdsa_deterministic': True} if subject_kind == 2 else {}
    if pss:
        options['rsa_padding'] = padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32)
    cert = builder.sign(subject, None if subject_kind == 1 else hashes.SHA256(), **options)
    raw = cert.public_bytes(serialization.Encoding.DER)
    peer = bytes([0, len(protobuf)]) + protobuf
    return dict(raw=raw, peer=peer, host=host_raw, host_seed=host_seed, seed=seed,
                subject=subject, host_kind=host_kind, subject_kind=subject_kind,
                signature_kind=4 if pss else subject_kind)


def authenticated_record(f):
    raw = f['raw']
    fields = parse(raw).children(raw)[0].children(raw)
    spki = fields[6]
    key_bits = spki.children(raw)[1]
    key_span = (key_bits.body + 1, key_bits.end - key_bits.body - 1)
    modulus, exponent = (0, 0), (0, 0)
    if f['subject_kind'] == 3:
        parts = parse(raw, key_span[0]).children(raw)
        def unsigned_span(node):
            start = node.body + (raw[node.body] == 0)
            return start, node.end - start
        modulus, exponent = map(unsigned_span, parts)
    words = [f['host_kind'], len(f['host']), len(f['peer']), f['subject_kind'],
             *key_span, *modulus, *exponent, len(raw), f['signature_kind']]
    return (struct.pack('<12Q', *words) + f['host'].ljust(40, b'\0')
            + f['peer'].ljust(40, b'\0') + b'\0' * 16)


def verify_certificate(f):
    cert = x509.load_der_x509_certificate(f['raw'])
    key = cert.public_key()
    if isinstance(key, ed25519.Ed25519PublicKey):
        key.verify(cert.signature, cert.tbs_certificate_bytes)
    elif isinstance(key, ec.EllipticCurvePublicKey):
        key.verify(cert.signature, cert.tbs_certificate_bytes, ec.ECDSA(hashes.SHA256()))
    else:
        key.verify(cert.signature, cert.tbs_certificate_bytes,
                   cert.signature_algorithm_parameters, cert.signature_hash_algorithm)
    return cert
