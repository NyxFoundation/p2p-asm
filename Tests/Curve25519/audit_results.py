#!/usr/bin/env python3
"""Reconcile completed executions with the current independent fixtures.

This audits persisted results; it does not replace executing check.py,
adversarial.py and iterate.py after production-code changes.
"""
import hashlib
import json
from importlib.metadata import version
from adversarial import negatives
from build import OUT
from cases import write_case
from fixtures import cases
from iterate import EXPECTED

KINDS = ('xpublic', 'xraw', 'xshared', 'edpublic', 'edsign', 'edverify')


def audit_case(directory, fresh, kind, case, index, code, model):
    recorded = directory / f'case-{index}'
    expected = write_case(fresh / f'case-{index}', kind, case, index)
    for name in ('a.bin', 'b.bin', 'before.bin', 'expected.bin', 'sizes.bin',
                 'meta.bin', 'name.txt'):
        assert (recorded / name).read_bytes() == (fresh / f'case-{index}' / name).read_bytes(), (
            kind, case.name, name, 'fixture changed since execution')
    for name in ('after.bin', 'protocol.native.bin', 'encoded.native.bin'):
        assert (recorded / name).read_bytes() == expected, (kind, case.name, name)
    for mode in ('protocol', 'encoded'):
        assert (recorded / f'{mode}.program.bin').read_bytes() == code
    steps = int((recorded / 'steps.txt').read_text())
    assert steps > 0
    assert f'PASS {kind} case {index}: {steps} steps' in model
    return steps


def audit_suite(kind, category):
    directory = OUT / category / kind
    fresh = OUT / 'fixture-audit' / (category or 'main') / kind
    fixtures = negatives(kind) if category else cases(kind)
    assert int((directory / 'count.txt').read_text()) == len(fixtures)
    code = (directory / 'encoded.bin').read_bytes()
    assert code == (directory / 'gnu.bin').read_bytes()
    assert code == (OUT / 'adversarial' / kind / 'encoded.bin').read_bytes()
    model = (directory / 'model.txt').read_text()
    steps = [audit_case(directory, fresh, kind, case, index, code, model)
             for index, case in enumerate(fixtures)]
    return {'algorithm': kind, 'category': category or 'main', 'cases': len(fixtures),
            'trace_pairs': sum(case.trace for case in fixtures),
            'qemu_executions': 2 * len(fixtures), 'instructions': len(code) // 4,
            'code_sha256': hashlib.sha256(code).hexdigest(),
            'model_steps': sum(steps), 'maximum_case_steps': max(steps)}


def audit_iteration():
    directory = OUT / 'iterations-1000'
    assert (directory / 'spec.bin').read_bytes() == EXPECTED
    expected = (b'\xa5' * 8 + EXPECTED + b'\x5a' * 8 + bytes(896) + b'\x5a' * 8
                + b'\x69' * 8 + bytes(272) + b'\x69' * 8)
    for mode in ('protocol', 'encoded'):
        assert (directory / f'{mode}.bin').read_bytes() == expected
    return {'iterations': 1000, 'qemu_executions': 2, 'lowered_model': False,
            'result': EXPECTED.hex()}


def main():
    reports = [audit_suite(kind, category) for category in ('', 'adversarial') for kind in KINDS]
    totals = {key: sum(report[key] for report in reports)
              for key in ('cases', 'trace_pairs', 'qemu_executions', 'model_steps')}
    result = {'oracle': 'cryptography==' + version('cryptography'), 'suites': reports,
              'totals': totals, 'rfc7748_iteration': audit_iteration()}
    (OUT / 'verification.json').write_text(json.dumps(result, indent=2) + '\n')
    print('PASS persisted execution audit: ' + json.dumps(totals))


if __name__ == '__main__':
    main()
