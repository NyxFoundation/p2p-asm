"""RFC9002 arithmetic, written independently using unbounded Python integers."""

GRANULARITY = 1_000_000


def rtt(previous, sample, raw_delay, exponent, maximum, confirmed, space):
    if previous is None:
        return sample, sample, sample, sample//2
    _, minimum, smoothed, variance = previous
    minimum = min(minimum, sample)
    delay = min(maximum, (raw_delay << exponent)*1000) if confirmed and space == 2 else 0
    adjusted = sample-delay if sample-minimum >= delay else sample
    return sample, minimum, (7*smoothed+adjusted)//8, (3*variance+abs(smoothed-adjusted))//4


def pto(smoothed, variance, maximum, confirmed, space, count):
    return (smoothed+max(4*variance,GRANULARITY)+(maximum if confirmed and space == 2 else 0)) << count


def published_examples():
    # RFC9002 §7.6.3: 1+4*0+0, clamped granularity, threshold 3.
    assert 3*pto(1_000_000,0,0,True,2,0) == 6_000_000
    # Published §7.6.3 timeline: lost #2 at t=1 through #8 at t=8,
    # acknowledged #9 at 12.2, assumed base duration 2: 7 > 2*3.
    assert (8-1) > 2*3
    assert not ((6-1) > 2*3)
    # Initial RTT from RFC9002 §A.2; variance initialized at half that value.
    assert pto(333_000_000,166_500_000,25_000_000,False,0,0) == 999_000_000
    assert pto(333_000_000,166_500_000,25_000_000,True,2,1) == 2_048_000_000
    assert rtt(None,100_000_000,0,3,25_000_000,True,2) == (
        100_000_000,100_000_000,100_000_000,50_000_000)
