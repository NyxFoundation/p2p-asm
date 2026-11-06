"""Cross-algorithm cryptographic and parser mutations, all using real signing."""
import copy
from cryptography import x509
from cryptography.x509.oid import ObjectIdentifier
from cryptography.hazmat.primitives import hashes
from cryptography.hazmat.primitives.asymmetric import ec, ed25519, padding
from oracle import certificate, parse, tlv, cv_signature, test_seed, host_signature, host_key
from cases import fixture, issue_fixture, base


def changed(cert, raw):
    return dict(cert, raw=raw)


def resign(cert, fields):
    raw = cert['raw']
    root = parse(raw).children(raw)
    body = tlv(48, b''.join(fields))
    key = cert['subject']
    if isinstance(key, ed25519.Ed25519PrivateKey):
        signature = key.sign(body)
    elif isinstance(key, ec.EllipticCurvePrivateKey):
        signature = key.sign(body, ec.ECDSA(hashes.SHA256(), deterministic_signing=True))
    else:
        scheme = (padding.PSS(mgf=padding.MGF1(hashes.SHA256()), salt_length=32)
                  if cert['signature_kind'] == 4 else padding.PKCS1v15())
        signature = key.sign(body, scheme, hashes.SHA256())
    algorithm = raw[root[1].start:root[1].end]
    return changed(cert, tlv(48, body + algorithm + tlv(3, b'\0' + signature)))


def tbs_fields(cert):
    raw = cert['raw']
    return [raw[n.start:n.end] for n in parse(raw).children(raw)[0].children(raw)]


def extension_mutation(cert, mode):
    fields = tbs_fields(cert)
    raw = fields[-1]
    sequence = parse(raw).children(raw)[0]
    values = [raw[n.start:n.end] for n in sequence.children(raw)]
    if mode == 'missing':
        values = values[1:]
    elif mode == 'duplicate':
        values = [values[0], *values]
    elif mode == 'bad-signed-key':
        values[0] = values[0][:-1] + bytes([values[0][-1] ^ 1])
    fields[-1] = tlv(163, tlv(48, b''.join(values)))
    return resign(cert, fields)


def semantic_cases(cert):
    cases = []
    def add(label, value=cert, **kwargs):
        cases.append(fixture('auth', label, value, **kwargs))
    add('expected-peer-mismatch', expected=b'\0' * len(cert['peer']), status=25)
    add('listener-expected-peer-mismatch', role=2, expected=b'\0' * 38, status=25)
    add('fraction-after-expiry', utc_ns=1900000000000000001, status=21)
    add('one-ns-before-validity', utc_ns=1699999999999999999, status=21)
    add('inclusive-notbefore', utc_ns=1700000000000000000)
    add('inclusive-notafter', utc_ns=1900000000000000000)
    for mode in ['missing', 'duplicate']:
        add(mode + '-identity-extension', extension_mutation(cert, mode), status=20)
    add('altered-host-signature', extension_mutation(cert, 'bad-signed-key'), status=24)
    raw = cert['raw']
    add('altered-self-signature', changed(cert, raw[:-1] + bytes([raw[-1] ^ 1])), status=23)
    mutated = bytearray(raw)
    mutated[raw.index(b'libp2p')] ^= 1
    add('altered-exact-tbs', changed(cert, bytes(mutated)), status=23)
    add('trailing-certificate', changed(cert, raw + raw), status=20)
    add('truncated-certificate', changed(cert, raw[:-1]), status=20)
    add('indefinite-der', changed(cert, b'\x30\x80' + raw[4:]), status=20)
    add('unknown-critical-extension', certificate(extra=[(
        x509.UnrecognizedExtension(ObjectIdentifier('1.2.3.4'), b'abc'), True)]), status=20)
    add('unknown-noncritical-extension', certificate(extra=[(
        x509.UnrecognizedExtension(ObjectIdentifier('1.2.3.4'), b'abc'), False)]))
    add('wrong-server-eku', certificate(eku=(2,)), status=22)
    add('wrong-client-eku', certificate(eku=(1,)), role=2, status=22)
    add('absent-eku-unrestricted', certificate(eku=None))
    public = cert['host']
    noncanonical = b'\x12\x20' + public + b'\x88\x00\x81\x00\x18\x01'
    add('canonical-peer-from-noncanonical-protobuf', certificate(host_proto=noncanonical))
    add('invalid-host-point', certificate(host_proto=b'\x08\x01\x12\x20' + b'\0' * 32), status=24)
    add('unsupported-host-key', certificate(host_proto=b'\x08\x03\x12\x20' + public), status=28)
    far = certificate(after=253402300799)
    fields = tbs_fields(far)
    fields[4] = tlv(48, tlv(24, b'00010101000000Z') + tlv(24, b'99991231235959Z'))
    for label, value in [('far-years-0001-9999', resign(far, fields)),
                         ('future-3000', certificate(before=32503680000, after=32535216000))]:
        add(label, value, status=21 if label == 'future-3000' else 0)
    # Canonical point/scalar checks must run even for apparently valid ASN.1.
    root = parse(raw).children(raw)
    sig_start = root[-1].body + 1
    order = 2**252 + 27742317777372353535851937790883648493
    bad_s = raw[:sig_start + 32] + order.to_bytes(32, 'little')
    add('ed-noncanonical-scalar', changed(cert, bad_s), status=23)
    bad_r = raw[:sig_start] + b'\0' * 32 + raw[sig_start + 32:]
    add('ed-invalid-signature-point', changed(cert, bad_r), status=23)
    fields = tbs_fields(cert)
    fields[6] = fields[6][:-32] + b'\0' * 32
    add('ed-invalid-subject-point', resign(cert, fields), status=23)
    return cases


def metadata_cases(cert):
    cases = []
    checks = [('chain-empty', {16: 0}, 1), ('chain-multiple', {16: 2}, 1),
              ('role-zero', {24: 0}, 26), ('role-three', {24: 3}, 26),
              ('empty-dial-peer', {48: 0}, 25), ('peer-length-overflow', {48: 2**64-1}, 25),
              ('output-short', {64: 191}, 5), ('length-narrowing', {8: 2**56}, 1),
              ('certificate-budget', {88: len(cert['raw'])-1}, 29),
              ('work-short', {80: 8192+16*len(cert['raw'])-1}, 5),
              ('stack-short', {136: 1551}, 5), ('work-alignment', {72: base(3)+9}, 4),
              ('input-wrap', {0: 2**64-2}, 4), ('output-wrap', {56: 2**64-1}, 4),
              ('work-wrap', {72: 2**64-8}, 4), ('expected-wrap', {40: 2**64-1}, 4),
              ('work-input-alias', {72: base(1)+8}, 4),
              ('output-input-alias', {56: base(1)+8}, 4),
              ('output-work-alias', {56: base(3)+8}, 4),
              ('descriptor-work-alias', {72: base(0)+8}, 4),
              ('output-stack-alias', {56: base(5)+3000}, 4)]
    for label, changes, status in checks:
        cases.append(fixture('auth', label, cert, changes=changes, status=status,
                             owned=False, check_spec=False))
    cases.append(fixture('auth', 'operation-budget-wipe', cert, changes={96: 1},
                         status=29, check_spec=False))
    cases.append(fixture('auth', 'host-byte-budget-wipe', cert, changes={104: 1},
                         status=29, check_spec=False))
    cases.append(fixture('auth', 'exact-output-capacity', cert, changes={64: 192}))
    return cases


def cv_cases(cert):
    digest = test_seed('transcript')
    signature = cv_signature(cert['subject'], 1, digest)
    values = [fixture('cv-verify', 'altered-role', cert, role=2, signature=signature, status=23),
              fixture('cv-verify', 'altered-transcript', cert, digest=b'\0' * 32,
                      signature=signature, status=23),
              fixture('cv-verify', 'signature-zero', cert, signature=b'\0' * 64, status=23)]
    for scheme in [0x0401, 0x0808, 0x0403, 0x0804, 0, 0x100000807]:
        values.append(fixture('cv-verify', f'unsupported-or-confused-{scheme}', cert,
                              changes={176: scheme}, status=27))
    values.append(fixture('cv-verify', 'signature-wrap', cert, changes={160: 2**64-1},
                          status=4, owned=False, check_spec=False))
    for length in [0, 31, 33, 2**64-1]:
        values.append(fixture('cv-verify', f'transcript-length-{length}', cert,
                              changes={152: length}, status=1, owned=False, check_spec=False))
    return values


def signing_cases(cert):
    values = [fixture('cv-sign', 'fresh-ed-client', cert, role=2)]
    for offset in [8, 152]:
        for length in [0, 31, 33, 2**64-1]:
            values.append(fixture('cv-sign', f'length-{offset}-{length}', cert,
                                  changes={offset: length}, status=1, owned=False, check_spec=False))
    for label, changes, status, owned in [
        ('output-short', {64: 63}, 5, False), ('seed-output-alias', {56: base(1)+8}, 4, False),
        ('seed-work-alias', {72: base(1)+8}, 4, False),
        ('budget-wipe', {96: 1}, 29, True)]:
        values.append(fixture('cv-sign', label, cert, changes=changes, status=status,
                              owned=owned, check_spec=False))
    return values


def issuance_cases(cert):
    values = [issue_fixture(certificate(host_kind=2), 'fresh-k256-certificate')]
    for before, after, label in [(1900000000, 1700000000, 'inverted-time'),
                                  (-62135596801, 1900000000, 'year-zero'),
                                  (1700000000, 253402300800, 'year-10000')]:
        values.append(issue_fixture(cert, label, status=21, before=before, after=after))
    for label, changes, status, owned in [
        ('entropy-length31', {56: 31}, 1, False), ('entropy-length33', {56: 33}, 1, False),
        ('entropy-length-u64', {56: 2**64-1}, 1, False), ('secret-length31', {8: 31}, 1, False),
        ('secret-output-short', {88: 31}, 5, False), ('peer-output-short', {136: 47}, 5, False),
        ('work-short', {104: 16383}, 5, False), ('unsupported-host', {16: 3}, 28, False),
        ('entropy-wrap', {48: 2**64-1}, 4, False), ('der-wrap', {64: 2**64-1}, 4, False),
        ('secret-entropy-alias', {80: base(1)+40}, 4, False),
        ('entropy-host-alias', {48: base(1)+8}, 4, False),
        ('der-secret-alias', {80: base(2)+8}, 4, False),
        ('budget-wipe', {112: 1}, 29, True),
        ('exact-der-capacity-minus-one', {72: len(cert['raw'])-1}, 5, True)]:
        values.append(issue_fixture(cert, label, changes=changes, status=status,
                                    owned=owned, check_spec=False))
    return values


def suites():
    cert = certificate()
    result = {name: [] for name in ['auth', 'cv-verify', 'cv-sign', 'issue']}
    for host in [1, 2]:
        for subject, pss in [(1, False), (2, False), (3, False), (3, True)]:
            value = certificate(host_kind=host, subject_kind=subject, pss=pss)
            for role in [1, 2]:
                label = f'host{host}-subject{subject}-pss{int(pss)}-role{role}'
                for kind in ['auth', 'cv-verify']:
                    result[kind].append(fixture(kind, label, value, role=role))
    result['auth'] += semantic_cases(cert) + metadata_cases(cert)
    result['cv-verify'] += cv_cases(cert)
    result['cv-sign'] += [fixture('cv-sign', 'fresh-ed-server', cert)] + signing_cases(cert)
    result['issue'] += [issue_fixture(cert, 'fresh-ed-certificate')] + issuance_cases(cert)
    return result
