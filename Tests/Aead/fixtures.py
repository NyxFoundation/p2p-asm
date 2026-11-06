"""Deterministic test-only fixtures. The external oracle is cryptography 49.0.0."""

import random
from cryptography.hazmat.primitives.ciphers import Cipher, algorithms, modes
from cryptography.hazmat.primitives.ciphers.aead import AESGCM
from vectors import AES, GCM, SBOX, SCHEDULE

RNG = random.Random(0xAEAD128)


def random_bytes(n):
    return bytes(RNG.randrange(256) for _ in range(n))


def expanded(key):
    result, rc = bytearray(key), 1
    for i in range(4, 44):
        t = result[-4:]
        if i % 4 == 0:
            t = bytearray(SBOX[x] for x in t[1:] + t[:1])
            t[0] ^= rc
            rc = ((rc << 1) ^ (0x11b if rc & 128 else 0)) & 255
        result += bytes(result[4*(i-4)+j] ^ t[j] for j in range(4))
    return bytes(result)


def aes(key, block):
    encryptor = Cipher(algorithms.AES(key), modes.ECB()).encryptor()
    return encryptor.update(block) + encryptor.finalize()


def fixture(label, *, key=b'', nonce=b'', aad=b'', data=b'', output=b'', expected=b'',
            status=0, alignment=0, trace_group='', **metadata):
    result = dict(label=label, key=list(key), nonce=list(nonce), aad=list(aad),
                  input=list(data), output=list(output), expected=list(expected), status=status,
                  keyLength=len(key), nonceLength=len(nonce), aadLength=len(aad),
                  inputLength=len(data), capacity=len(output), workspaceCapacity=1280,
                  alignment=alignment, traceGroup=trace_group)
    result.update(metadata)
    return result


def aes_cases():
    results = {kind: [] for kind in ('sbox', 'expand', 'aes', 'hp', 'ghash')}
    for i in range(16):
        data = bytes(range(16*i, 16*i+16))
        results['sbox'].append(fixture(f'all-bytes-{i}', output=data,
                                      expected=bytes(SBOX[x] for x in data), trace_group='all-sbox'))
    assert expanded(SCHEDULE[:16]) == SCHEDULE
    pairs = [(bytes.fromhex(k), bytes.fromhex(p), bytes.fromhex(c)) for k, p, c in AES]
    pairs += [(random_bytes(16), random_bytes(16), None) for _ in range(8)]
    for i, (key, data, known) in enumerate(pairs):
        actual = aes(key, data)
        assert known is None or known == actual
        for kind, result in [('expand', expanded(key)), ('aes', actual), ('hp', actual[:5])]:
            results[kind].append(fixture(f'vector-{i}', key=key if kind == 'expand' else expanded(key),
                data=data, output=b'\xcc'*len(result), expected=result, alignment=i % 8,
                workspaceCapacity=1024, trace_group=f'{kind}-{i%8}'))
    # Capacity checks, malformed sizes, no memory mutation on validation errors.
    for kind, outlen in [('expand', 176), ('aes', 16), ('hp', 5)]:
        key = bytes(16) if kind == 'expand' else expanded(bytes(16))
        for label, status, override in [('output-short', 3, {'capacity': outlen-1}),
                                        ('workspace-short', 4, {'workspaceCapacity': 1023}),
                                        ('length-bad', 1 if kind == 'expand' else 2,
                                         {'keyLength' if kind == 'expand' else 'inputLength': 15})]:
            output = random_bytes(outlen)
            results[kind].append(fixture(label, key=key, data=bytes(16), output=output,
                expected=output, status=status, **override))
    # Polynomial oracle here is intentionally test-only; GCM's cryptography
    # oracle supplies independent validation of composition/multiplication too.
    for i in range(8):
        h, block, acc = random_bytes(16), random_bytes(16), random_bytes(16)
        x, v, z = int.from_bytes(block, 'big') ^ int.from_bytes(acc, 'big'), int.from_bytes(h, 'big'), 0
        for bit in range(127, -1, -1):
            if (x >> bit) & 1:
                z ^= v
            v = (v >> 1) ^ (0xe1000000000000000000000000000000 if v & 1 else 0)
        results['ghash'].append(fixture(f'mul-{i}', key=h, data=block, output=acc,
                                       expected=z.to_bytes(16, 'big'), alignment=i))
    return results


def make_gcm(label, key, nonce, aad, plain, alignment=0, known=None):
    sealed = AESGCM(key).encrypt(nonce, plain, aad)
    assert known is None or sealed == known
    group = f'gcm-{len(aad)}-{len(plain)}-{alignment}'
    seal = fixture(label, key=key, nonce=nonce, aad=aad, data=plain,
                   output=bytes([0xaa])*len(sealed), expected=sealed,
                   alignment=alignment, trace_group=group)
    opening = fixture(label, key=key, nonce=nonce, aad=aad, data=sealed,
                      output=bytes([0xbb])*len(plain), expected=plain,
                      alignment=alignment, trace_group=group)
    return seal, opening


def gcm_cases():
    results = {'seal': [], 'open': []}
    for i, vector in enumerate(GCM):
        key, nonce, aad, plain, known = map(bytes.fromhex, vector)
        seal, opening = make_gcm(f'nist-{i}', key, nonce, aad, plain, i % 8, known)
        results['seal'].append(seal)
        results['open'].append(opening)
    lengths = [0, 1, 15, 16, 17, 31, 32, 33, 65, 129]
    for i, n in enumerate(lengths):
        args = (random_bytes(16), random_bytes(12), random_bytes(lengths[-1-i]), random_bytes(n))
        seal, opening = make_gcm(f'random-{n}', *args, alignment=i%8)
        results['seal'].append(seal)
        results['open'].append(opening)
    # Equal public layout, changing all secret contents plus invalid tags/AAD/IV.
    key, nonce, aad, plain = random_bytes(16), random_bytes(12), random_bytes(17), random_bytes(33)
    seal, good = make_gcm('trace-success', key, nonce, aad, plain)
    results['seal'].append(seal)
    results['open'].append(good)
    for field, indexes in [('input', [0, 16, *range(33, 49)]), ('aad', [0, 16]), ('nonce', [0, 11])]:
        for index in indexes:
            bad = {**good, 'label': f'tampered-{field}-{index}', 'status': 6,
                   'expected': good['output'].copy(), field: good[field].copy()}
            bad[field][index] ^= 1
            results['open'].append(bad)
    for variant in range(2):
        s, o = make_gcm(f'trace-secret-{variant}', random_bytes(16), random_bytes(12),
                        random_bytes(17), random_bytes(33))
        results['seal'].append(s)
        results['open'].append(o)
    for n in range(16):
        results['open'].append(fixture(f'short-tag-{n}', key=key, nonce=nonce, data=bytes(n),
                               output=bytes(4), expected=bytes(4), status=3, capacity=0))
    add_invalid_gcm(results, seal, good)
    return results


def add_invalid_gcm(results, seal, good):
    # Huge lengths are metadata only; guards verify no payload reads or writes.
    for kind, original in [('seal', seal), ('open', good)]:
        for label, status, overrides in [
            ('key-length', 1, {'keyLength': 15}), ('nonce-length', 2, {'nonceLength': 11}),
            ('message-bound', 4, {'inputLength': (1 << 36)-31 + (16 if kind == 'open' else 0)}),
            ('maximum-u64', 4, {'inputLength': (1 << 64)-1}),
            ('aad-bound', 5, {'aadLength': 1 << 61}),
            ('output-short', 7, {'capacity': len(original['output'])-1}),
            ('workspace-short', 8, {'workspaceCapacity': 1279}),
            ('max-message-reaches-capacity', 7,
             {'inputLength': (1 << 36)-32 + (16 if kind == 'open' else 0), 'capacity': 0}),
            ('max-aad-reaches-capacity', 7, {'aadLength': (1 << 61)-1, 'capacity': 0})]:
            results[kind].append({**original, 'label': label, 'status': status,
                                  'expected': original['output'], 'traceGroup': '', **overrides})
