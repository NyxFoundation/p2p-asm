import Libp2pAsm.Spec.Identity.X509.Der

namespace Libp2pAsm.Spec.Identity.X509

def edOid : List UInt8 := [43, 101, 112]
def ecOid : List UInt8 := [42, 134, 72, 206, 61, 2, 1]
def p256Oid : List UInt8 := [42, 134, 72, 206, 61, 3, 1, 7]
def ecdsaOid : List UInt8 := [42, 134, 72, 206, 61, 4, 3, 2]
def rsaOid : List UInt8 := [42, 134, 72, 134, 247, 13, 1, 1, 1]
def pkcsOid : List UInt8 := [42, 134, 72, 134, 247, 13, 1, 1, 11]
def pssOid : List UInt8 := [42, 134, 72, 134, 247, 13, 1, 1, 10]
def mgfOid : List UInt8 := [42, 134, 72, 134, 247, 13, 1, 1, 8]
def sha256Oid : List UInt8 := [96, 134, 72, 1, 101, 3, 4, 2, 1]

private def sha256Algorithm (bytes : List UInt8) (node : Node) : Except Error Unit := do
  if node.tag != 0x30 then throw .algorithm
  let (id, rest) ← oid bytes node.children
  if id != sha256Oid then throw .algorithm
  nullOrAbsent bytes rest

private def pssHash (bytes : List UInt8) (cursor : Cursor) : Except Error Cursor := do
  let (outer, rest) ← expect bytes cursor 0xa0
  let (inner, endHash) ← expect bytes outer.children 0x30
  finished endHash
  sha256Algorithm bytes inner
  return rest

private def pssMask (bytes : List UInt8) (cursor : Cursor) : Except Error Cursor := do
  let (outer, rest) ← expect bytes cursor 0xa1
  let (inner, endMask) ← expect bytes outer.children 0x30
  finished endMask
  let (id, params) ← oid bytes inner.children
  if id != mgfOid then throw .algorithm
  let (hash, done) ← expect bytes params 0x30
  finished done
  sha256Algorithm bytes hash
  return rest

private def explicitInteger (bytes : List UInt8) (cursor : Cursor) (tag value : Nat) :
    Except Error Cursor := do
  let (outer, rest) ← expect bytes cursor tag
  let (inner, done) ← expect bytes outer.children 2
  finished done
  if inner.content.bytes bytes != [value.toUInt8] then throw .algorithm
  return rest

/-- TLS's SHA256/MGF1-SHA256/salt32 PSS profile. RFC4055 requires accepting
an explicit trailerField1 as well as its absent default. SHA256 AlgorithmIdentifier
parameters may be absent or NULL. Defaults SHA1/salt20 are not this profile. -/
private def pssParameters (bytes : List UInt8) (cursor : Cursor) : Except Error Unit := do
  let (params, done) ← expect bytes cursor 0x30
  finished done
  let cursor ← pssHash bytes params.children
  let cursor ← pssMask bytes cursor
  let cursor ← explicitInteger bytes cursor 0xa2 32
  let cursor ← if cursor.offset == cursor.stop then pure cursor
    else explicitInteger bytes cursor 0xa3 1
  finished cursor

/-- Codes: Ed25519=1, ECDSA/P256/SHA256=2, RSA/PKCS1/SHA256=3,
RSA/PSS/SHA256=4. This checks AlgorithmIdentifier, not the signature. -/
def signatureAlgorithm (bytes : List UInt8) : Except Error Nat := do
  let root ← whole bytes 0x30
  let (id, params) ← oid bytes root.children
  if id == edOid || id == ecdsaOid then
    if params.offset != params.stop then throw .algorithm
    return if id == edOid then 1 else 2
  if id == pkcsOid then
    nullOrAbsent bytes params
    return 3
  if id == pssOid then
    pssParameters bytes params
    return 4
  throw .algorithm

/-- Codes: Ed25519=1, P256=2, rsaEncryption=3. PSS-restricted key OIDs are
not advertised as rsa_pss_rsae and cannot be substituted for rsaEncryption. -/
def publicKeyAlgorithm (bytes : List UInt8) : Except Error Nat := do
  let root ← whole bytes 0x30
  let (id, params) ← oid bytes root.children
  if id == edOid then
    if params.offset != params.stop then throw .algorithm
    return 1
  if id == rsaOid then
    nullOrAbsent bytes params
    return 3
  if id == ecOid then
    let (curve, done) ← oid bytes params
    finished done
    if curve != p256Oid then throw .algorithm
    return 2
  throw .algorithm

end Libp2pAsm.Spec.Identity.X509
