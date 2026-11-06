import Libp2pAsm.Rv64.Logic.WordStore

namespace Libp2pAsm.Rv64.Logic

theorem wordByte_bits (value : Word) (byte bit : Nat) :
    (BitVec.ofNat 64 (wordByte value byte).toNat).getLsbD bit =
      (decide (bit < 8) && value.getLsbD (8*byte+bit)) := by
  simp only [wordByte, Nat.toUInt8_eq, UInt8.toNat_ofNat', BitVec.getLsbD_ofNat,
    Nat.testBit_mod_two_pow, BitVec.toNat_ushiftRight, Nat.testBit_shiftRight]
  by_cases h : bit < 8
  · simp [h, show bit < 64 by omega, Nat.add_comm, BitVec.getLsbD]
  · simp [h]

theorem readLE64_writeLE64 (bytes : Array UInt8) (offset : Nat) (value : Word)
    (hb : offset+8 ≤ bytes.size) : readLE64 (writeLE64 bytes offset value) offset = value := by
  simp only [readLE64, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [writeLE64_byte bytes offset value 0 hb (by decide),
    writeLE64_byte bytes offset value 1 hb (by decide),
    writeLE64_byte bytes offset value 2 hb (by decide),
    writeLE64_byte bytes offset value 3 hb (by decide),
    writeLE64_byte bytes offset value 4 hb (by decide),
    writeLE64_byte bytes offset value 5 hb (by decide),
    writeLE64_byte bytes offset value 6 hb (by decide),
    writeLE64_byte bytes offset value 7 hb (by decide)]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, wordByte_bits]
  by_cases h0 : i < 8
  · simp [h0, hi, show i < 16 by omega, show i < 24 by omega,
      show i < 32 by omega, show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  by_cases h1 : i < 16
  · simp [h0, h1, hi, show i-8 < 8 by omega, show 8+(i-8)=i by omega,
      show i < 24 by omega, show i < 32 by omega, show i < 40 by omega,
      show i < 48 by omega, show i < 56 by omega]
  by_cases h2 : i < 24
  · simp [h0, h1, h2, hi, show ¬i-8 < 8 by omega, show i-16 < 8 by omega,
      show 16+(i-16)=i by omega, show i < 32 by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  by_cases h3 : i < 32
  · simp [h0, h1, h2, h3, hi, show ¬i-8 < 8 by omega, show ¬i-16 < 8 by omega,
      show i-24 < 8 by omega, show 24+(i-24)=i by omega,
      show i < 40 by omega, show i < 48 by omega, show i < 56 by omega]
  by_cases h4 : i < 40
  · simp [h0, h1, h2, h3, h4, hi, show ¬i-8 < 8 by omega, show ¬i-16 < 8 by omega,
      show ¬i-24 < 8 by omega, show i-32 < 8 by omega, show 32+(i-32)=i by omega,
      show i < 48 by omega, show i < 56 by omega]
  by_cases h5 : i < 48
  · simp [h0, h1, h2, h3, h4, h5, hi, show ¬i-8 < 8 by omega, show ¬i-16 < 8 by omega,
      show ¬i-24 < 8 by omega, show ¬i-32 < 8 by omega, show i-40 < 8 by omega,
      show 40+(i-40)=i by omega, show i < 56 by omega]
  by_cases h6 : i < 56
  · simp [h0, h1, h2, h3, h4, h5, h6, hi, show ¬i-8 < 8 by omega,
      show ¬i-16 < 8 by omega, show ¬i-24 < 8 by omega, show ¬i-32 < 8 by omega,
      show ¬i-40 < 8 by omega, show i-48 < 8 by omega, show 48+(i-48)=i by omega]
  · simp [h0, h1, h2, h3, h4, h5, h6, hi, show ¬i-8 < 8 by omega,
      show ¬i-16 < 8 by omega, show ¬i-24 < 8 by omega, show ¬i-32 < 8 by omega,
      show ¬i-40 < 8 by omega, show ¬i-48 < 8 by omega,
      show i-56 < 8 by omega, show 56+(i-56)=i by omega]

end Libp2pAsm.Rv64.Logic
