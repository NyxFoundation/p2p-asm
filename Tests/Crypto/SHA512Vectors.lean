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

namespace Libp2pAsm.Tests.Crypto.SHA512Vectors

private def vector0 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=0", 0,
    "",
    ("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f" ++
      "63b931bd47417a81a538327af927da3e")⟩

private def vector1 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=8", 1,
    "21",
    ("3831a6a6155e509dee59a7f451eb35324d8f8f2df6e3708894740f98fdee23889f4de5adb0c5010dfb555cda77c8ab5d" ++
      "c902094c52de3278f35a75ebc25f093a")⟩

private def vector2 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=880", 110,
    ("10f2be77a4055771a67007cd8630e3230e38288499cb160380290174d66da57455b6baaa9785c84c8a663de41ed3bd54" ++
      "4055b9170cec43cb3eb120eceaba1fe36e3eaa3fa4f99b425cd2519f09bc0282bada52d14ce625b1ded3b24d86b1dad3" ++
      "42d2b7be322b775b04fc6b86afb4"),
    ("a872fa33d463b3343cec57c20c66979c33e1ad067bfc703454696aab5dd0003bc194318f4a8ebbc74503feb7211a472d" ++
      "adee991efe3e38f21a1310f8a76eac80")⟩

private def vector3 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=888", 111,
    ("324533e685f1852e358eea8ea8b81c288b3f3beb1f2bc2b8d3fdbac318382e3d7120de30c9c237aa0a34831deb1e5e06" ++
      "0a7969cd3a9742ec1e64b354f7eb290cba1c681c66cc7ea994fdf5614f604d1a2718aab581c1c94931b1387e4b7dc736" ++
      "35bf3a7301174075fa70a9227d85d3"),
    ("3b26c5170729d0814153becb95f1b65cd42f9a6d0649d914e4f69d938b5e9dc041cd0f5c8da0b484d7c7bc7b1bdefb08" ++
      "fe8b1bfedc81109345bc9e9a399feedf")⟩

private def vector4 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=896", 112,
    ("518985977ee21d2bf622a20567124fcbf11c72df805365835ab3c041f4a9cd8a0ad63c9dee1018aa21a9fa3720f47dc4" ++
      "8006f1aa3dba544950f87e627f369bc2793ede21223274492cceb77be7eea50e5a509059929a16d33a9f54796cde5770" ++
      "c74bd3ecc25318503f1a41976407aff2"),
    ("c00926a374cde55b8fbd77f50da1363da19744d3f464e07ce31794c5a61b6f9c85689fa1cfe136553527fd876be91673" ++
      "c2cac2dd157b2defea360851b6d92cf4")⟩

private def vector5 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=904", 113,
    ("9159767275ba6f79cbb3d58c0108339d8c6a41138991ab7aa58b14793b545b04bda61dd255127b12cc501d5aaad476e0" ++
      "9fa14aec21626e8d57b7d08c36cdb79eea314bdd77e65779a0b54eab08c48ceb976adf631f4246a33f7ef896887ea8b5" ++
      "dfa2087a225c8c180f8970696101fc283b"),
    ("3cd3380a90868de17dee4bd4d7f90d7512696f0a92b2d089240d61a9d20cd3af094c78bf466c2d404dd2f662ec5f4a29" ++
      "9be2adeadf627b98e50e1c072b769d62")⟩

private def vector6 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=1016", 127,
    ("c13e6ca3abb893aa5f82c4a8ef754460628af6b75af02168f45b72f8f09e45ed127c203bc7bb80ff0c7bd96f8cc6d811" ++
      "0868eb2cfc01037d8058992a6cf2effcbfe498c842e53a2e68a793867968ba18efc4a78b21cdf6a11e5de821dcabab14" ++
      "921ddb33625d48a13baffad6fe8272dbdf4433bd0f7b813c981269c388f001"),
    ("6e56f77f6883d0bd4face8b8d557f144661989f66d51b1fe4b8fc7124d66d9d20218616fea1bcf86c08d63bf8f2f2184" ++
      "5a3e519083b937e70aa7c358310b5a7c")⟩

private def vector7 : HashVector :=
  ⟨"NIST CAVP SHA512ShortMsg Len=1024", 128,
    ("fd2203e467574e834ab07c9097ae164532f24be1eb5d88f1af7748ceff0d2c67a21f4e4097f9d3bb4e9fbf97186e0db6" ++
      "db0100230a52b453d421f8ab9c9a6043aa3295ea20d2f06a2f37470d8a99075f1b8a8336f6228cf08b5942fc1fb4299c" ++
      "7d2480e8e82bce175540bdfad7752bc95b577f229515394f3ae5cec870a4b2f8"),
    ("a21b1077d52b27ac545af63b32746c6e3c51cb0cb9f281eb9f3580a6d4996d5c9917d2a6e484627a9d5a06fa1b25327a" ++
      "9d710e027387fc3e07d7c4d14c6086cc")⟩

private def vector8 : HashVector :=
  ⟨"NIST CAVP SHA512LongMsg Len=1816", 227,
    ("4f05600950664d5190a2ebc29c9edb89c20079a4d3e6bc3b27d75e34e2fa3d02768502bd69790078598d5fcf3d6779bf" ++
      "ed1284bbe5ad72fb456015181d9587d6e864c940564eaafb4f2fead4346ea09b6877d9340f6b82eb1515880872213da3" ++
      "ad88feba9f4f13817a71d6f90a1a17c43a15c038d988b5b29edffe2d6a062813cedbe852cde302b3e33b696846d2a8e3" ++
      "6bd680efcc6cd3f9e9a4c1ae8cac10cc5244d131677140399176ed46700019a004a163806f7fa467fc4e17b4617bbd76" ++
      "41aaff7ff56396ba8c08a8be100b33a20b5daf134a2aefa5e1c3496770dcf6baa4f7bb"),
    ("a9db490c708cc72548d78635aa7da79bb253f945d710e5cb677a474efc7c65a2aab45bc7ca1113c8ce0f3c32e1399de9" ++
      "c459535e8816521ab714b2a6cd200525")⟩

def all : List HashVector :=
  [vector0, vector1, vector2, vector3, vector4, vector5, vector6, vector7, vector8]

end Libp2pAsm.Tests.Crypto.SHA512Vectors

