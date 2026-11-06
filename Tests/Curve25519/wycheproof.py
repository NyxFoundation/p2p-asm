"""Selected official fields; fixed commit/content pin in provenance.json.
Apache-2.0: LICENSES/Curve25519-Wycheproof.txt. No runtime dependency.
"""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
DATA=(HERE/'wycheproof-selected.json').read_bytes()
PROVENANCE=json.loads((HERE/'provenance.json').read_text())
assert hashlib.sha256(DATA).hexdigest()==PROVENANCE['wycheproof']['selected_sha256']
RECORDS=json.loads(DATA)['tests']
STATUS={1:0,10:11,63:10,85:10,151:10}
ED=[(r['tcId'],r['key'],r['msg'],r['sig'],STATUS[r['tcId']])
    for r in RECORDS if r['algorithm']=='Ed25519']
X=[(r['tcId'],r['private'],r['public'],r['shared'])
   for r in RECORDS if r['algorithm']=='X25519']
