"""Deterministic arbitrary syntax inputs; no case-count coverage assertion."""
import random
from cases import fixture


def cases(kind):
    rng=random.Random({'packet':9000,'frame':9001,'tp':1819}[kind])
    result=[]
    for i in range(96):
        size=rng.randrange(65)
        data=bytes(rng.randrange(256) for _ in range(size))
        option=rng.randrange(21) if kind=='packet' else rng.randrange(2)
        result.append(fixture(kind,f'fuzz-{kind}-{i}',data,option,64))
    return result
