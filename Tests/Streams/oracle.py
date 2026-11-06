"""Independent dictionary-based protocol oracle (never imported by runtime)."""
from dataclasses import dataclass, field, replace
MAX = (1 << 62) - 1
NONE = (1 << 64) - 1

@dataclass
class Receive:
    cap: int = 8
    base: int = 0
    highest: int = 0
    final: int = NONE
    limit: int = MAX
    allowance: int = MAX
    crypto: int = 0
    reset: int = 0
    data: dict = field(default_factory=dict)

    def put(self, off, payload, flag=0):
        end = off + len(payload)
        if flag > 2 or (self.crypto and flag) or (flag == 2 and payload):
            return 1, self, 0
        if off > MAX or end > MAX:
            return 2, self, 0
        if self.final != NONE and (end > self.final or (flag and end != self.final)):
            return 4, self, 0
        if flag and end < self.highest:
            return 4, self, 0
        delta = max(end, self.highest) - self.highest
        if not self.crypto and (end > self.limit or delta > self.allowance):
            return 3, self, 0
        active = {off+i: b for i, b in enumerate(payload) if off+i >= self.base}
        if flag != 2 and not self.reset and active and end - self.base > self.cap:
            return (7 if self.crypto else 6), self, 0
        if not self.reset and any(k in self.data and self.data[k] != v for k,v in active.items()):
            return 5, self, 0
        state = replace(self, highest=max(self.highest, end),
                        final=end if flag else self.final,
                        reset=int(flag == 2 or self.reset),
                        data={} if flag == 2 else dict(self.data) if self.reset else self.data | active)
        return 0, state, 0 if self.crypto else delta

    def peek(self):
        end = self.base
        while end in self.data and end % self.cap >= self.base % self.cap:
            end += 1
            if end % self.cap == 0:
                break
        return self.base % self.cap, end - self.base

    def consume(self, n):
        if any(k not in self.data for k in range(self.base, self.base+n)):
            return 8, self
        return 0, replace(self, base=self.base+n,
                          data={k:v for k,v in self.data.items() if k >= self.base+n})
