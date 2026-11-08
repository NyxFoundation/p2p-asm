"""ABI fixtures and independent complete snapshots. Seed material is test-only."""
import struct
from oracle import certificate, authenticated_record, cv_signature, test_seed

WORD = (1 << 64) - 1


def base(i):
    return 0x200000 + 0x100000 * i


def guarded(raw):
    return b'\xa5' * 8 + raw + b'\x5a' * 8


def fixture(kind, label, cert, role=1, status=0, owned=True, changes=None,
            utc_ns=1800000000000000000, expected=None, digest=None, signature=None,
            spec_status=None, check_spec=True):
    raw = cert['raw'] if kind != 'cv-sign' else cert['seed']
    digest = test_seed('transcript') if digest is None else digest
    scheme = {1: 0x0807, 2: 0x0403, 3: 0x0804}[cert['subject_kind']]
    signature = cv_signature(cert['subject'], role, digest) if signature is None else signature
    expected = (cert['peer'] if role == 1 else b'') if expected is None else expected
    input_bytes = raw + digest + signature + expected
    work_size = 8192 + 16 * len(raw)
    fields = [base(1) + 8, len(raw), 1, role, utc_ns & WORD,
              base(1) + 8 + len(raw) + len(digest) + len(signature), len(expected),
              base(2) + 8, 768, base(3) + 8, work_size, len(raw),
              1_000_000_000, len(raw), len(raw), len(raw), 2048, 1552,
              base(1) + 8 + len(raw), len(digest),
              base(1) + 8 + len(raw) + len(digest), len(signature), scheme, 0]
    for offset, value in (changes or {}).items():
        fields[offset // 8] = value & WORD
    regions = [guarded(struct.pack('<24Q', *fields)), guarded(input_bytes),
               guarded(b'\xcc' * 768), guarded(b'\xcc' * work_size),
               guarded(b'\xdd'), b'\x69' * 4112]
    expected_regions = list(regions)
    if owned:
        expected_regions[3] = guarded(b'\0' * work_size)
        expected_regions[5] = b'\x69' * (4096 - 1552) + b'\0' * 1552 + b'\x69' * 16
    result, output = b'', b''
    if status == 0:
        if kind == 'auth':
            output, result = authenticated_record(cert), cert['peer']
        elif kind == 'cv-sign':
            output = result = cv_signature(cert['subject'], role, digest)
        expected_regions[2] = guarded(output + b'\xcc' * (768 - len(output)))
    reads = [[base(0) + 8, 192]]
    writes = []
    if owned:
        reads += [[base(1) + 8, len(input_bytes)], [base(3) + 8, work_size],
                  [base(5) + 4096 - 1552, 1552]]
        writes += [[base(3) + 8, work_size], [base(5) + 4096 - 1552, 1552]]
    if output:
        writes += [[base(2) + 8, len(output)]]
    return dict(label=label, regions=[list(r) for r in regions],
                expectedRegions=[list(r) for r in expected_regions],
                args=[base(0) + 8] + [0] * 7, outputs=[status],
                reads=reads, writes=writes, budget=100_000_000,
                raw=list(cert['raw']), seed=list(cert['seed']), digest=list(digest),
                host=list(cert['host_seed']), hostKind=cert['host_kind'],
                notBefore=1700000000, notAfter=1900000000,
                signature=list(signature), expectedPeer=list(expected), result=list(result),
                role=role, scheme=fields[22], utcNs=utc_ns, checkSpec=check_spec,
                specStatus=status if spec_status is None else spec_status)


def smoke():
    cert = certificate()
    return {
        'auth': [fixture('auth', 'ed-host-ed-subject-server', cert)],
        'cv-verify': [fixture('cv-verify', 'ed-server', cert)],
        'cv-sign': [fixture('cv-sign', 'fresh-ed-server', cert)],
        'issue': [issue_fixture(cert, 'fresh-ed-certificate')],
    }


def issue_fixture(cert, label, status=0, owned=True, changes=None, check_spec=True,
                  spec_status=None, before=1700000000, after=1900000000):
    fields = [base(1) + 8, 32, cert['host_kind'], 0, before & WORD, after & WORD,
              base(1) + 40, 32, base(2) + 8, len(cert['raw']), base(2) + 520, 32,
              base(3) + 8, 16384, 1_000_000_000, 1552, base(2) + 560, 48] + [0] * 6
    for offset, value in (changes or {}).items():
        fields[offset // 8] = value & WORD
    regions = [guarded(struct.pack('<24Q', *fields)), guarded(cert['host_seed'] + cert['seed']),
               guarded(b'\xcc' * 768), guarded(b'\xcc' * 16384),
               guarded(b'\xdd'), b'\x69' * 4112]
    expected_regions = list(regions)
    reads, writes = [[base(0) + 8, 192]], []
    if owned:
        expected_regions[3] = guarded(b'\0' * 16384)
        expected_regions[5] = b'\x69' * (4096 - 1552) + b'\0' * 1552 + b'\x69' * 16
        reads += [[base(1) + 8, 64], [base(3) + 8, 16384], [base(5) + 2544, 1552]]
        writes += [[base(3) + 8, 16384], [base(5) + 2544, 1552]]
    if status == 0:
        output = bytearray(regions[2])
        peer_record = struct.pack('<Q', len(cert['peer'])) + cert['peer'].ljust(40, b'\0')
        for offset, payload in [(8, cert['raw']), (520, cert['seed']), (560, peer_record)]:
            output[offset:offset + len(payload)] = payload
            writes.append([base(2) + offset, len(payload)])
        expected_regions[2] = bytes(output)
    return dict(label=label, regions=[list(r) for r in regions],
                expectedRegions=[list(r) for r in expected_regions],
                args=[base(0) + 8] + [0] * 7,
                outputs=[status, len(cert['raw']) if status == 0 else 0],
                reads=reads, writes=writes, budget=100_000_000,
                raw=list(cert['raw']), seed=list(cert['seed']), host=list(cert['host_seed']),
                hostKind=cert['host_kind'], digest=[], signature=[], expectedPeer=[],
                result=list(cert['raw']) if status == 0 else [], role=1, scheme=0x0807,
                utcNs=1800000000000000000, notBefore=before, notAfter=after,
                checkSpec=check_spec, specStatus=status if spec_status is None else spec_status)
