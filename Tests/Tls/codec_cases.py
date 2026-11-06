"""Published TLS bytes plus independent profile and adversarial wire fixtures."""
from dataclasses import dataclass, field
import json
from pathlib import Path
from codec_oracle import decode, Error, HRR


def u(width, n): return n.to_bytes(width, 'big')
def vec(width, data): return u(width, len(data))+data
def ext(kind, data): return u(2, kind)+vec(2, data)
def msg(kind, data): return bytes([kind])+vec(3, data)


def client(extensions=None, session=b'', suites=b'\x13\x01', compression=b'\0', version=0x0303):
    extensions = standard_extensions() if extensions is None else extensions
    return msg(1, u(2, version)+bytes(range(32))+vec(1, session)+vec(2, suites)
               +vec(1, compression)+vec(2, b''.join(extensions)))


def standard_extensions():
    return [ext(43, vec(1, b'\x03\x04')), ext(10, vec(2, b'\0\x1d\0\x17')),
            ext(51, vec(2, b'\0\x1d'+vec(2, bytes(range(32))))),
            ext(13, vec(2, b'\x04\x03\x08\x04\x04\x01\x08\x07')),
            ext(16, vec(2, vec(1, b'libp2p'))), ext(57, b'\0\0')]


def server(retry=False, extensions=None, session=b'', suite=0x1301, version=0x0303, compression=0):
    if extensions is None:
        share = b'\0\x17' if retry else b'\0\x1d'+vec(2, bytes(range(32)))
        extensions = [ext(43, b'\x03\x04'), ext(51, share)]
    return msg(2, u(2, version)+(HRR if retry else bytes(range(32)))+vec(1, session)
               +u(2, suite)+bytes([compression])+vec(2, b''.join(extensions)))


def cert(data=b'opaque DER owned by integrator', context=b'', entries=1, extensions=b''):
    entry = vec(3, data)+vec(2, extensions)
    return msg(11, vec(1, context)+vec(3, entry*entries))


@dataclass(frozen=True)
class CodecCase:
    name: str
    a: bytes
    strict: bool = True
    limit: int = 2**24-1
    fault: str = ''
    overrides: dict = field(default_factory=dict)
    b: bytes = b''
    error_code: int = 0

    @property
    def status(self):
        if self.error_code: return self.error_code
        if self.fault: return 5 if self.fault in ('out-cap', 'work-cap') else 4
        try: decode(self.a, self.limit, self.strict)
        except Error as e: return e.code
        return 0

    @property
    def processed(self):
        return not self.error_code and not self.fault and len(self.a) >= 4 and self.status not in (1, 9)


def base_cases():
    result = []
    records = json.loads(Path(__file__).with_name('rfc8448.json').read_text())
    for section, rows in records.items():
        for i, row in enumerate(rows):
            if row['field'] in ('ClientHello', 'ServerHello', 'EncryptedExtensions', 'CertificateRequest',
                                'Certificate', 'CertificateVerify', 'Finished', 'NewSessionTicket'):
                result.append(CodecCase(f'rfc8448-{section}-{i}-{row["field"]}', bytes.fromhex(row['hex']), False))
    profiles = {'client': client(), 'server': server(), 'retry': server(True),
        'ee': msg(8, vec(2, ext(16, vec(2, vec(1, b'libp2p')))+ext(57, b'params'))),
        'request': msg(13, b'\0'+vec(2, ext(13, vec(2, b'\x04\x03\x08\x04\x08\x07')))),
        'cert': cert(), 'verify': msg(15, b'\x08\x07'+vec(2, bytes(64))),
        'finished': msg(20, bytes(32)),
        'ticket': msg(4, u(4, 604800)+u(4, 2**32-1)+vec(1, b'nonce')+vec(2, b'ticket')+vec(2, ext(42, u(4, 0xffffffff))))}
    result += [CodecCase(name, data) for name, data in profiles.items()]
    return result, profiles


def cases(extended=False):
    result, profiles = base_cases()
    from go_oracle import load, messages
    for trace in load():
        result += [CodecCase('go-'+trace['Name']+'-'+who+'-'+str(i), wire)
                   for i,(who,wire) in enumerate(messages(trace))]
        for i,event in enumerate(trace['Events']):
            if event['Kind'] != 'write': continue
            flight = bytes.fromhex(event['Data'])
            offset = 0
            while offset < len(flight):
                result.append(CodecCase(f'flight-{trace["Name"]}-{i}-{offset}',flight[offset:]))
                offset += 4+int.from_bytes(flight[offset+1:offset+4],'big')
    ex = standard_extensions()
    wires = {'unknown-client': client(ex+[ext(0xffff, bytes(range(255)))]),
        'ignored-sni': client(ex+[ext(0, b'opaque ignored SNI')]),
        'duplicate-unknown': client(ex+[ext(65000, b''), ext(65000, b'')]),
        'duplicate-known': client(ex+[ex[0]]), 'session-max': client(session=bytes(32)),
        'session-too-long': client(session=bytes(33)), 'version': client(version=0x0301),
        'no-compression': client(compression=b''), 'bad-compression': client(compression=b'\x01'),
        'multi-compression': client(compression=b'\0\0'), 'no-suites': client(suites=b''),
        'odd-suites': client(suites=b'\x13'), 'wrong-suite': client(suites=b'\x13\x02'),
        'server-suite': server(suite=0x1302), 'server-version': server(version=0x0301),
        'server-compression': server(compression=1), 'server-session-long': server(session=bytes(33)),
        'hrr-cookie-only': server(True, [ext(43,b'\x03\x04'),ext(44,vec(2,b'cookie'))]),
        'hrr-empty-cookie': server(True, [ext(43,b'\x03\x04'),ext(44,b'\0\0')]),
        'hrr-empty': server(True, [ext(43,b'\x03\x04')]),
        'hrr-share': server(True, [ext(43,b'\x03\x04'),ext(51,b'\0\x17\0')]),
        'server-unknown': server(extensions=[ext(43,b'\x03\x04'),ext(123,b'')]),
        'empty-cert': cert(entries=0), 'two-certs': cert(entries=2),
        'cert-wrong-extension-context': cert(extensions=ext(51,b'')),
        'ee-early-data': msg(8,vec(2,ext(42,b''))),
        'ticket-wrong-extension-context': msg(4,u(4,1)+u(4,0)+b'\0'+vec(2,b'x')+vec(2,ext(43,b'\x03\x04'))),
        'empty-der': cert(data=b''), 'cert-context': cert(context=b'x'),
        'cert-duplicate-ext': cert(extensions=ext(999,b'')*2),
        'cert-large': cert(data=bytes(65536)),
        'cv-rsa-pkcs1': msg(15,b'\x04\x01'+vec(2,b'x')),
        'cv-empty': msg(15,b'\x08\x07\0\0'), 'keyupdate': msg(24,b'\0'),
        'finished-short': msg(20,bytes(31)), 'finished-long': msg(20,bytes(33)),
        'unknown-ee-obligation': msg(8,vec(2,ext(16,vec(2,vec(1,b'libp2p')))+ext(57,b'params')+ext(0xfff0,b'unsolicited-check-required'))),
        'wrong-ee-context': msg(8,vec(2,ext(43,b'\x03\x04'))),
        'duplicate-unknown-share': client([ext(51,vec(2,(b'\xfe\x00'+vec(2,b'x'))*2)) if int.from_bytes(e[:2],'big') == 51 else e for e in ex]),
        'ticket-lifetime': msg(4,u(4,604801)+u(4,0)+b'\0'+vec(2,b'x')+b'\0\0')}
    for slot in range(len(ex)):
        wires[f'missing-{slot}'] = client(ex[:slot]+ex[slot+1:])
    for kind, data in [(43,b'\0'),(43,b'\x01\x03'),(43,b'\x02\x03\x03'),
        (10,b'\0\0'),(10,b'\0\x01\0'),(13,b'\0\0'),(13,vec(2,b'\x04\x01')),
        (51,b'\0\0'),(51,vec(2,b'\0\x1d'+vec(2,bytes(31)))),
        (51,vec(2,(b'\0\x1d'+vec(2,bytes(32)))*2)),
        (51,vec(2,b'\0\x17'+vec(2,b'\x04'+bytes(64)))),
        (51,vec(2,b'\0\x17'+vec(2,b'\x02'+bytes(64)))),
        (16,b'\0\0'),(16,vec(2,vec(1,b'wrong'))),(16,vec(2,b'\0'))]:
        replacement = [ext(kind,data) if int.from_bytes(e[:2],'big') == kind else e for e in ex]
        wires[f'extension-{kind}-{len(wires)}'] = client(replacement)
    result += [CodecCase(name, wire) for name, wire in wires.items()]
    for name, wire in profiles.items():
        result.append(CodecCase(f'concatenated-{name}', wire+profiles['finished']))
        for n in range(len(wire)):
            result.append(CodecCase(f'truncated-{name}-{n}', wire[:n]))
        for n in range(4,len(wire)):
            result.append(CodecCase(f'inner-truncated-{name}-{n}',wire[:1]+u(3,n-4)+wire[4:n]))
        result.append(CodecCase(f'inner-overrun-{name}', wire[:1]+u(3,len(wire)-5)+wire[4:]))
        result.append(CodecCase(f'trailing-body-{name}', wire[:1]+u(3,len(wire)-3)+wire[4:]+b'\0'))
    result += [CodecCase('bad-profile-flag',profiles['client'],overrides={7:2},error_code=2)]
    result += [CodecCase('uint24-max-incomplete', b'\x0b\xff\xff\xff'),
               CodecCase('caller-limit', profiles['cert'], limit=4)]
    for fault in ('out-cap','work-cap','input-wrap','out-wrap','work-wrap','overlap','work-input',
                  'out-work','stack-work','desc-align','desc-wrap','work-align','stack-align','stack-underflow'):
        result.append(CodecCase(fault, profiles['client'], fault=fault))
    retry = server(True)
    for i in range(32):
        changed = retry[:6+i]+bytes([retry[6+i]^1])+retry[7+i:]
        result.append(CodecCase(f'edge-hrr-random-byte-{i}',changed))
    result += [CodecCase('edge-duplicate-extension-ffff',client(ex+[ext(65535,b'')]*2)),
               CodecCase('edge-duplicate-share-ffff',client([ext(51,vec(2,(b'\xff\xff'+vec(2,b'x'))*2)) if int.from_bytes(e[:2],'big') == 51 else e for e in ex])),
               CodecCase('edge-full-uint16-extensions',msg(8,vec(2,ext(65535,bytes(65531)))),False)]
    if extended:
        source = [c for c in result if c.name.startswith(('rfc8448-', 'go-'))]
        prefixes = {c.a for c in result if c.name.startswith('truncated-')}
        for c in source:
            for n in range(len(c.a)):
                wire = c.a[:n]
                if wire in prefixes: continue
                prefixes.add(wire)
                result.append(CodecCase('every-prefix-'+c.name+'-'+str(n),wire,c.strict))
    return result
