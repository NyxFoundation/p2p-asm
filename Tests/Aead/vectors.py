"""Public AES/GCM known answers: FIPS 197, SP 800-38A and NIST GCM examples."""

# FIPS 197-upd1, Table 4. Test data only; production ASM has no lookup table.
SBOX = bytes.fromhex('''
63 7c 77 7b f2 6b 6f c5 30 01 67 2b fe d7 ab 76
ca 82 c9 7d fa 59 47 f0 ad d4 a2 af 9c a4 72 c0
b7 fd 93 26 36 3f f7 cc 34 a5 e5 f1 71 d8 31 15
04 c7 23 c3 18 96 05 9a 07 12 80 e2 eb 27 b2 75
09 83 2c 1a 1b 6e 5a a0 52 3b d6 b3 29 e3 2f 84
53 d1 00 ed 20 fc b1 5b 6a cb be 39 4a 4c 58 cf
d0 ef aa fb 43 4d 33 85 45 f9 02 7f 50 3c 9f a8
51 a3 40 8f 92 9d 38 f5 bc b6 da 21 10 ff f3 d2
cd 0c 13 ec 5f 97 44 17 c4 a7 7e 3d 64 5d 19 73
60 81 4f dc 22 2a 90 88 46 ee b8 14 de 5e 0b db
e0 32 3a 0a 49 06 24 5c c2 d3 ac 62 91 95 e4 79
e7 c8 37 6d 8d d5 4e a9 6c 56 f4 ea 65 7a ae 08
ba 78 25 2e 1c a6 b4 c6 e8 dd 74 1f 4b bd 8b 8a
70 3e b5 66 48 03 f6 0e 61 35 57 b9 86 c1 1d 9e
e1 f8 98 11 69 d9 8e 94 9b 1e 87 e9 ce 55 28 df
8c a1 89 0d bf e6 42 68 41 99 2d 0f b0 54 bb 16
''')

AES = [
    ('000102030405060708090a0b0c0d0e0f', '00112233445566778899aabbccddeeff',
     '69c4e0d86a7b0430d8cdb78070b4c55a'),
    ('2b7e151628aed2a6abf7158809cf4f3c', '3243f6a8885a308d313198a2e0370734',
     '3925841d02dc09fbdc118597196a0b32'),
    ('2b7e151628aed2a6abf7158809cf4f3c', '6bc1bee22e409f96e93d7e117393172a',
     '3ad77bb40d7a3660a89ecaf32466ef97'),
]

# NIST AES_GCM.pdf examples 1, 2, 3, 5 (AES128). P512 is also the complete
# plaintext in the original GCM submission's 96-bit-IV examples.
KEY = 'feffe9928665731c6d6a8f9467308308'
IV = 'cafebabefacedbaddecaf888'
P512 = ('d9313225f88406e5a55909c5aff5269a8'
        '6a7a9531534f7da2e4c303d8a318a721'
        'c3c0c95956809532fcf0e2449a6b525b'
        '16aedf5aa0de657ba637b391aafd255')
C512 = ('42831ec2217774244b7221b784d0d49c'
        'e3aa212f2c02a4e035c17e2329aca12e'
        '21d514b25466931c7d8f6a5aac84aa05'
        '1ba30b396a0aac973d58e091473f5985')
AAD512 = ('3ad77bb40d7a3660a89ecaf32466ef97'
          'f5d3d58503b9699de785895a96fdbaaf'
          '43b1cd7f598ece23881b00e3ed030688'
          '7b0c785e27e8ad3f8223207104725dd4')
GCM = [
    (KEY, IV, '', '', '3247184b3c4f69a44dbcd22887bbb418'),
    (KEY, IV, '', P512, C512 + '4d5c2af327cd64a62cf35abd2ba6fab4'),
    (KEY, IV, AAD512, '', '5f91d77123ef5eb9997913849b8dc1e9'),
    (KEY, IV, AAD512[:40], P512[:-8],
     C512[:-8] + 'f07c2528eea2fca1211f905e1b6a881b'),
    ('00'*16, '00'*12, '', '', '58e2fccefa7e3061367f1d57a4e7455a'),
    ('00'*16, '00'*12, '', '00'*16,
     '0388dace60b6a392f328c2b971b2fe78ab6e47d42cec13bdf53a67b21257bddf'),
]

# FIPS 197 Appendix A.1: all eleven round keys.
SCHEDULE = bytes.fromhex('''
2b7e151628aed2a6abf7158809cf4f3c
a0fafe1788542cb123a339392a6c7605
f2c295f27a96b9435935807a7359f67f
3d80477d4716fe3e1e237e446d7a883b
ef44a541a8525b7fb671253bdb0bad00
d4d1c6f87c839d87caf2b8bc11f915bc
6d88a37a110b3efddbf98641ca0093fd
4e54f70e5f5fc9f384a64fb24ea6dc4f
ead27321b58dbad2312bf5607f8d292f
ac7766f319fadc2128d12941575c006e
d014f9a8c9ee2589e13f0cc8b6630ca6
''')
