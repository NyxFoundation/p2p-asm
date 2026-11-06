import Tests.Crypto.Support

/-!
Published NIST CAVP byte-oriented SHA vectors (CAVS 11.0, 2011-03-15).
Empty-message records say Msg=00 but Len=0; the input below is correctly [].
Selection includes the padding transition, full block boundary, and LongMsg.
Original archive:
https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/shs/shabytetestvectors.zip
Mirror used to retrieve unchanged records:
https://github.com/pyca/cryptography/tree/f05ec395898cb8aab11bc583ee3d8014d0914755/vectors/cryptography_vectors/hashes/SHA2
Expected digests are published data, not computed by the implementation.
-/

namespace Libp2pAsm.Tests.Crypto.SHA256Vectors

private def vector0 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=0", 0,
    "",
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"⟩

private def vector1 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=8", 1,
    "d3",
    "28969cdfa74a12c82f3bad960b0b000aca2ac329deea5c2328ebc6f2ba9802c1"⟩

private def vector2 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=432", 54,
    ("25362a4b9d74bde6128c4fdc672305900947bc3ada9d9d316ebcf1667ad4363189937251f149c72e064a48608d940b75" ++
      "74b17fefc0df"),
    "f8e4ccab6c979229f6066cc0cb0cfa81bb21447c16c68773be7e558e9f9d798d"⟩

private def vector3 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=440", 55,
    ("3ebfb06db8c38d5ba037f1363e118550aad94606e26835a01af05078533cc25f2f39573c04b632f62f68c294ab31f2a3" ++
      "e2a1a0d8c2be51"),
    "6595a2ef537a69ba8583dfbf7f5bec0ab1f93ce4c8ee1916eff44a93af5749c4"⟩

private def vector4 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=448", 56,
    ("2d52447d1244d2ebc28650e7b05654bad35b3a68eedc7f8515306b496d75f3e73385dd1b002625024b81a02f2fd6dffb" ++
      "6e6d561cb7d0bd7a"),
    "cfb88d6faf2de3a69d36195acec2e255e2af2b7d933997f348e09f6ce5758360"⟩

private def vector5 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=456", 57,
    ("4cace422e4a015a75492b3b3bbfbdf3758eaff4fe504b46a26c90dacc119fa9050f603d2b58b398cad6d6d9fa922a154" ++
      "d9e0bc4389968274b0"),
    "4d54b2d284a6794581224e08f675541c8feab6eefa3ac1cfe5da4e03e62f72e4"⟩

private def vector6 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=504", 63,
    ("e2f76e97606a872e317439f1a03fcd92e632e5bd4e7cbc4e97f1afc19a16fde92d77cbe546416b51640cddb92af99653" ++
      "4dfd81edb17c4424cf1ac4d75aceeb"),
    "18041bd4665083001fba8c5411d2d748e8abbfdcdfd9218cb02b68a78e7d4c23"⟩

private def vector7 : HashVector :=
  ⟨"NIST CAVP SHA256ShortMsg Len=512", 64,
    ("5a86b737eaea8ee976a0a24da63e7ed7eefad18a101c1211e2b3650c5187c2a8a650547208251f6d4237e661c7bf4c77" ++
      "f335390394c37fa1a9f9be836ac28509"),
    "42e61e174fbb3897d6dd6cef3dd2802fe67b331953b06114a65c772859dfc1aa"⟩

private def vector8 : HashVector :=
  ⟨"NIST CAVP SHA256LongMsg Len=1304", 163,
    ("451101250ec6f26652249d59dc974b7361d571a8101cdfd36aba3b5854d3ae086b5fdd4597721b66e3c0dc5d8c606d96" ++
      "57d0e323283a5217d1f53f2f284f57b85c8a61ac8924711f895c5ed90ef17745ed2d728abd22a5f7a13479a462d71b56" ++
      "c19a74a40b655c58edfe0a188ad2cf46cbf30524f65d423c837dd1ff2bf462ac4198007345bb44dbb7b1c861298cdf61" ++
      "982a833afc728fae1eda2f87aa2c9480858bec"),
    "3c593aa539fdcdae516cdf2f15000f6634185c88f505b39775fb9ab137a10aa2"⟩

def all : List HashVector :=
  [vector0, vector1, vector2, vector3, vector4, vector5, vector6, vector7, vector8]

end Libp2pAsm.Tests.Crypto.SHA256Vectors

