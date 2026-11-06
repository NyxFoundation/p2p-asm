"""QUIC envelope classification cannot be inferred from handshake byte 20."""
from dataclasses import dataclass, field


@dataclass(frozen=True)
class Case:
    name: str
    a: bytes
    status: int
    b: bytes = b''
    processed: bool = False
    fault: str = ''
    overrides: dict = field(default_factory=dict)


def cases():
    return [Case('handshake-'+str(t),bytes([0,t]),3 if t == 24 else 0)
            for t in (1,2,4,8,11,13,15,20,24)] + [
            Case('record-'+str(t),bytes([1,t]),3) for t in (20,21,22,23)]
