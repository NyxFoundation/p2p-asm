"""Structural and independently signed certificate fixtures, all test-only."""
from reference import patterns, LIBP2P


def tlv(tag, data):
    n = len(data)
    length = bytes((n,)) if n < 128 else (
        bytes((128+(n.bit_length()+7)//8,))+n.to_bytes((n.bit_length()+7)//8, "big"))
    return bytes((tag,))+length+data


def seq(*items):
    return tlv(48, b"".join(items))


def ext(identifier, data, critical=None):
    flag = b"" if critical is None else tlv(1, b"\xff" if critical else b"\x00")
    return seq(tlv(6, identifier), flag, tlv(4, data))


def identity():
    return ext(LIBP2P, seq(tlv(4, bytes.fromhex("08011220")+b"\x21"*32),
                          tlv(4, b"\x31"*64)), True)


def name(tag=12, value=b"parser test"):
    return seq(tlv(49, seq(patterns.oid("2.5.4.3"), tlv(tag, value))))


def make(*, signature=None, public=None, key=None, issuer=None, subject=None,
         extensions=None, serial=None, validity=None, version=None,
         tbs_extra=b"", root_extra=b"", spki_extra=b"", outer_signature=None, signature_bits=None):
    signature = signature if signature is not None else patterns.algorithm("1.3.101.112")
    public = public if public is not None else patterns.algorithm("1.3.101.112")
    key = key if key is not None else b"\x41"*32
    issuer = issuer if issuer is not None else name()
    subject = subject if subject is not None else name()
    validity = validity if validity is not None else seq(
        tlv(23, b"700101000000Z"), tlv(24, b"99991231235959Z"))
    serial = serial if serial is not None else tlv(2, b"\x01")
    version = version if version is not None else tlv(160, tlv(2, b"\x02"))
    extensions = [identity()] if extensions is None else extensions
    tbs = seq(version, serial, signature, issuer, validity, subject,
              seq(public, tlv(3, b"\x00"+key), spki_extra), tlv(163, seq(*extensions)), tbs_extra)
    return seq(tbs, signature if outer_signature is None else outer_signature,
               tlv(3, b"\x00"+b"\x51"*64) if signature_bits is None else signature_bits,
               root_extra)


def signed():
    from cryptography import x509
    from cryptography.hazmat.primitives import hashes, serialization
    from cryptography.hazmat.primitives.asymmetric import ed25519, ec, rsa, padding
    from datetime import datetime, timezone
    result = []
    host = ed25519.Ed25519PrivateKey.from_private_bytes(b"\x13"*32)
    host_raw = host.public_key().public_bytes_raw()
    pb = bytes.fromhex("08011220")+host_raw
    keys = [("ed", ed25519.Ed25519PrivateKey.from_private_bytes(b"\x14"*32), None),
            ("p256", ec.derive_private_key(17, ec.SECP256R1()), hashes.SHA256()),
            ("rsa-pkcs", rsa.generate_private_key(public_exponent=65537, key_size=2048),
             hashes.SHA256())]
    keys.append(("rsa-pss", keys[-1][1], hashes.SHA256()))
    for label, key, digest in keys:
        spki = key.public_key().public_bytes(serialization.Encoding.DER,
                                            serialization.PublicFormat.SubjectPublicKeyInfo)
        extension = seq(tlv(4, pb), tlv(4, host.sign(b"libp2p-tls-handshake:"+spki)))
        dn = x509.Name([x509.NameAttribute(x509.NameOID.COMMON_NAME, "libp2p parser")])
        builder = (x509.CertificateBuilder().subject_name(dn).issuer_name(dn)
                   .serial_number(7).public_key(key.public_key())
                   .not_valid_before(datetime(1950, 1, 1, tzinfo=timezone.utc))
                   .not_valid_after(datetime(9999, 12, 31, tzinfo=timezone.utc))
                   .add_extension(x509.UnrecognizedExtension(
                       x509.ObjectIdentifier("1.3.6.1.4.1.53594.1.1"), extension), critical=True))
        kwargs = {"rsa_padding": padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32)
                  } if label == "rsa-pss" else {}
        cert = builder.sign(key, digest, **kwargs)
        result.append((label, cert.public_bytes(serialization.Encoding.DER)))
    return result
