"""Raw-body/vector encoders and QUIC-envelope admission tests."""
from dataclasses import dataclass, field
from codec_cases import base_cases, client, standard_extensions, ext, CodecCase, msg, vec
from codec_oracle import decode, Error


@dataclass(frozen=True)
class EncodeCase:
    name: str
    a: bytes
    tag: int
    strict: bool = True
    limit: int = 2**24-1
    fault: str = ''
    overrides: dict = field(default_factory=dict)
    b: bytes = b''
    error_code: int = 0

    @property
    def status(self):
        if self.error_code: return self.error_code
        if self.fault: return 5 if self.fault in ('out-cap','work-cap') else 4
        try:
            view = decode(bytes([self.tag])+len(self.a).to_bytes(3,'big')+self.a, self.limit, self.strict)
            if int.from_bytes(view[440:448],'little'): return 7
        except Error as e: return e.code
        return 0

    @property
    def processed(self): return not self.error_code and not self.fault and len(self.a) <= self.limit


def cases():
    _, profiles = base_cases()
    result = [EncodeCase(name, wire[4:], wire[0]) for name,wire in profiles.items()]
    result += [EncodeCase('sni-emission',client(standard_extensions()+[ext(0,b'ignored')])[4:],1),
               EncodeCase('invalid-body',b'\0',1),EncodeCase('keyupdate',b'\0',24),
               EncodeCase('limit',profiles['cert'][4:],11,limit=4)]
    for fault in ('out-cap','work-cap','input-wrap','out-wrap','work-wrap','overlap','work-input',
                  'out-work','stack-work','desc-align','desc-wrap','work-align','stack-align','stack-underflow'):
        result.append(EncodeCase(fault,profiles['client'][4:],1,fault=fault))
    result += [EncodeCase('edge-large-extensions',vec(2,ext(65535,bytes(65531))),8,strict=False)]
    result += [EncodeCase('uint24-overflow',b'',1,overrides={1:2**24},error_code=2),
               EncodeCase('type-overflow',b'',1,overrides={2:256},error_code=2),
               EncodeCase('bad-profile-flag',b'',1,overrides={8:2},error_code=2),
               EncodeCase('uint24-max-capacity',b'',1,overrides={1:2**24-1,4:0},error_code=5)]
    return result


@dataclass(frozen=True)
class VectorCase:
    name: str
    a: bytes
    width: int
    minimum: int = 0
    limit: int = 2**24-1
    fault: str = ''
    overrides: dict = field(default_factory=dict)
    b: bytes = b''
    strict: bool = False

    @property
    def status(self):
        if self.fault: return 5 if self.fault == 'out-cap' else 4
        n = self.overrides.get(1,len(self.a))
        if self.width not in (1,2,3) or not self.minimum <= n < 256**self.width: return 2
        if n > self.limit: return 9
        return 0

    @property
    def processed(self): return self.status == 0


def vectors():
    result = [VectorCase(f'width-{w}-size-{n}',bytes(i%256 for i in range(n)),w)
              for w in (1,2,3) for n in (0,1,31,255) if n < 256**w]
    result += [VectorCase('uint16-max',bytes(65535),2),VectorCase('uint24-65536',bytes(65536),3),
               VectorCase('uint8-overflow',bytes(256),1),VectorCase('uint16-overflow',b'',2,overrides={1:65536}),
               VectorCase('uint24-overflow',b'',3,overrides={1:2**24}),
               VectorCase('zero-width',b'',0),VectorCase('four-width',b'',4),
               VectorCase('empty-required',b'',2,minimum=1),VectorCase('caller-limit',bytes(33),3,limit=32)]
    for fault in ('out-cap','input-wrap','out-wrap','overlap','desc-align','desc-wrap'):
        result.append(VectorCase(fault,bytes(32),3,fault=fault))
    return result
