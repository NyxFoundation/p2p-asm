# ASM-core chain integration

`Tests/Pipeline` connects five frozen leaves through **lowered RV64IM
instruction sequences** in the Lean machine model, using a genuine RFC 9001
Initial packet:

1. `Asm.Crypto.Quic.Kdf.derive .initial` derives Initial secrets/keys from the
   real destination CID.
2. `Asm.Crypto.Quic.Packet.unprotect` removes header protection, reconstructs
   the packet number and authenticates AES-128-GCM.
3. `Asm.Quic.Wire.packetParse` parses the unprotected Initial header into its
   descriptor.
4. `Asm.Quic.Wire.frameParse` parses the CRYPTO frame.
5. `Asm.Tls.Codec.decode` decodes the ClientHello (libp2p profile).

The Python fixture protects the packet with cryptography 49 AES primitives and
hand-rolled RFC 9001 HKDF labels (cross-checked against cryptography HKDF), and
computes the full expected memory. The probe checks every stage's status
registers, output buffers, owned-stack wipes, preserved registers, and the
complete final region/stack snapshots against Python's independent model.

## Reproduce

```sh
python3 Tests/Pipeline/check.py
```

Requires Lean 4.33.0 (Lake-managed native probe under ignored `build/pipeline/`).

## Scope and honesty

- Each leaf already has GNU byte equality and both QEMU paths in its own suite
  (`Tests/QuicCrypto`, `Tests/QuicWire`, `Tests/Tls`). This chain itself runs
  in the Lean model only; it adds **wiring** evidence, not new QEMU coverage.
- The packet is deliberately shorter than 1200 bytes: minimum-datagram and
  amplification rules are **caller obligations** of the connection core, which
  does not exist yet. This is not a state machine; there is no reassembly,
  ACK, retry, address validation or authentication decision here.
- The ClientHello is structural and profile-valid; identity, key agreement and
  Finished are not exercised. The 255-byte share/public keys are opaque bytes.
- Bounds quoted per stage are engineering estimates, not proved instruction
  bounds; the probe measures actual steps and asserts the estimate.
