"""Nested value/error-priority and date-digit branches, not only outer mutations."""
from fixtures import make, seq, tlv, name
from reference import patterns


def date_cases(case):
    result = []
    for tag, raw in ((23, b"000229235959Z"), (24, b"20000229235959Z")):
        end = tlv(24, b"99991231235959Z")
        for i in range(len(raw)):
            for invalid in (ord("/"), ord(":")):
                value = raw[:i]+bytes((invalid,))+raw[i+1:]
                result.append(case(f"date-digit-{tag}-{i}-{invalid}",
                                   make(validity=seq(tlv(tag, value), end))))
        for invalid_tag in (22, 25):
            result.append(case(f"date-tag-{tag}-{invalid_tag}",
                               make(validity=seq(tlv(invalid_tag, raw), end))))
    dates = [b"00000101000000Z", b"19000229000000Z", b"21000229000000Z",
             b"20000001000000Z", b"20001301000000Z", b"20000100000000Z",
             b"20000132000000Z", b"20000101240000Z", b"20000101006000Z",
             b"20000101000060Z", b"20000230000000Z", b"20000431000000Z",
             b"20000101000000", b"20000101000000ZZ", b"20000101000000z"]
    result += [case(f"date-field-{i}", make(validity=seq(tlv(24, raw),
                        tlv(24, b"99991231235959Z")))) for i, raw in enumerate(dates)]
    return result


def nested_cases(case):
    result = []
    rsa_sig = patterns.algorithm("1.2.840.113549.1.1.11", b"\x05\0")
    rsa_pub = patterns.algorithm("1.2.840.113549.1.1.1", b"\x05\0")
    values = (b"", b"\x80", b"\0\x01", b"\0\x80", b"\0", b"\x01")
    for i, value in enumerate(values):
        for field in (0, 1):
            integers = [tlv(2, b"\x01"), tlv(2, b"\x01")]
            integers[field] = tlv(2, value)
            result.append(case(f"rsa-integer-{field}-{i}",
                               make(signature=rsa_sig, public=rsa_pub, key=seq(*integers))))
    for label, key, extra in (
        ("rsa-missing-exponent-before-bad-modulus", seq(tlv(2, b"\x80")), b""),
        ("spki-extra-before-truncated-rsa", b"\x30", tlv(5, b"")),
        ("rsa-extra-before-bad-modulus", seq(tlv(2, b"\x80"), tlv(2, b"\1"), tlv(5, b"")), b""),
        ("rsa-wrong-root", tlv(4, b"\1"), b"")):
        result.append(case(label, make(signature=rsa_sig, public=rsa_pub, key=key,
                                       spki_extra=extra)))
    first = seq(patterns.oid("2.5.4.3"), tlv(12, b"z"*20))
    missing = seq(patterns.oid("2.5.4.3"))
    result.append(case("missing-attribute-value-before-unsorted",
                       make(subject=seq(tlv(49, first+missing)))))
    for i, oid in enumerate((b"", b"\x80", b"\x81", b"\x80\x01", b"\x81\0")):
        subject = seq(tlv(49, seq(tlv(6, oid), tlv(12, b"v"))))
        result.append(case(f"name-oid-{i}", make(subject=subject)))
    for i, raw in enumerate((b"\xff", b"\xc2A", b"\xe1\x80A", b"\xf1\x80\x80A",
                             b"\xf0\x8f\xbf\xbf", b"\xf4\x90\x80\x80",
                             b"\xed\x9f\xbf", b"\xf0\x90\x80\x80")):
        result.append(case(f"utf8-continuation-{i}", make(subject=name(12, raw))))
    return result
