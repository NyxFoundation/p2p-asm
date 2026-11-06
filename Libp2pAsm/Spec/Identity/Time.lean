import Std
import Std.Time.Date.PlainDate

/-! RFC5280 section4.1.2.5: UTC/GeneralizedTime with seconds and Z, no fractions.
Unix seconds use the proleptic Gregorian calendar, years1..9999. Leap-second
spelling is rejected rather than silently normalized into another timestamp. -/
namespace Libp2pAsm.Spec.Identity.Time

inductive Error where
  | length | invalid | range | capacity | notYetValid | expired
  deriving BEq, DecidableEq, Repr

def Error.code : Error → Nat
  | .length => 1 | .range => 4 | .capacity => 5 | .invalid => 6
  | .notYetValid => 7 | .expired => 8

def leap (year : Nat) : Bool := year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

def daysBeforeYear (year : Nat) : Nat :=
  let y := year-1
  365*y + y/4 - y/100 + y/400

def daysBeforeMonth (year month : Nat) : Nat :=
  (367*month-362)/12 - (if month ≤ 2 then 0 else if leap year then 1 else 2)

def monthDays (year month : Nat) : Nat :=
  if month == 2 then if leap year then 29 else 28
  else if [4, 6, 9, 11].contains month then 30 else 31

def decimal (bytes : List UInt8) : Except Error Nat :=
  bytes.foldlM (fun n b =>
    if b.toNat < 48 || b.toNat > 57 then .error .invalid
    else .ok (10*n + b.toNat-48)) 0

def civilSeconds (year month day hour minute second : Nat) : Except Error Int := do
  if year == 0 || year > 9999 || month == 0 || month > 12 then throw .invalid
  if day == 0 || day > monthDays year month then throw .invalid
  if hour ≥ 24 || minute ≥ 60 || second ≥ 60 then throw .invalid
  let days := Int.ofNat (daysBeforeYear year + daysBeforeMonth year month + day-1) - 719162
  return days*86400 + (hour*3600+minute*60+second : Nat)

/-- Body bytes only. Accept either ASN.1 time tag; the encoder chooses the canonical tag. -/
def decode (tag : Nat) (bytes : List UInt8) : Except Error Int := do
  if tag != 0x17 && tag != 0x18 then throw .invalid
  let width := if tag == 0x17 then 2 else 4
  if bytes.length != width+11 then throw .length
  if bytes.getLast? != some 90 then throw .invalid
  let yy ← decimal (bytes.take width)
  let year := if tag == 0x17 then yy + (if yy < 50 then 2000 else 1900) else yy
  let month ← decimal (bytes.drop width |>.take 2)
  let day ← decimal (bytes.drop (width+2) |>.take 2)
  let hour ← decimal (bytes.drop (width+4) |>.take 2)
  let minute ← decimal (bytes.drop (width+6) |>.take 2)
  let second ← decimal (bytes.drop (width+8) |>.take 2)
  civilSeconds year month day hour minute second

def digits (n width : Nat) : List UInt8 :=
  (List.range width).map fun i => (48 + n / 10^(width-1-i) % 10).toUInt8

/-- Complete DER TLV, using UTCTime1950..2049, GeneralizedTime otherwise. -/
def encode (seconds : Int) : Except Error (List UInt8) := do
  if seconds < -62135596800 || seconds > 253402300799 then throw .invalid
  let date := Std.Time.PlainDate.ofEpochDay (.ofInt (seconds/86400))
  let year := date.year.toInt.toNat
  let month := date.month.toInt.toNat
  let day := date.day.toInt.toNat
  let clock := (seconds % 86400).toNat
  let utc := 1950 ≤ year && year ≤ 2049
  let width := if utc then 2 else 4
  return [if utc then 0x17 else 0x18, (width+11).toUInt8] ++
    digits year width ++ digits month 2 ++ digits day 2 ++
    digits (clock/3600) 2 ++ digits (clock/60 % 60) 2 ++ digits (clock%60) 2 ++ [90]

/-- Exact inclusive validity in nanoseconds. Trust in the wall-clock source is
a caller obligation, not established by this numeric comparison. -/
def validity (notBefore notAfter utcNs : Int) : Except Error Unit := do
  if notAfter < notBefore then throw .invalid
  if utcNs < notBefore*1000000000 then throw .notYetValid
  if notAfter*1000000000 < utcNs then throw .expired

end Libp2pAsm.Spec.Identity.Time
