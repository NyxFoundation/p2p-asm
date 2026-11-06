import Libp2pAsm.Asm.Arithmetic
import Libp2pAsm.Asm.Crypto.SHA256
import Libp2pAsm.Asm.Crypto.SHA512
import Libp2pAsm.Asm.Crypto.HKDF
import Libp2pAsm.Asm.Crypto.TlsKdf
import Libp2pAsm.Asm.Crypto.AES.Api
import Libp2pAsm.Asm.Crypto.GCM.Api
import Libp2pAsm.Asm.Crypto.Curve25519.X25519
import Libp2pAsm.Asm.Crypto.Curve25519.Ed25519
import Libp2pAsm.Asm.Crypto.Curve25519.Verify
import Libp2pAsm.Asm.Crypto.Weierstrass.Ecdsa
import Libp2pAsm.Asm.Codec.Der
import Libp2pAsm.Asm.Identity.PublicKey
import Libp2pAsm.Asm.Identity.Time
import Libp2pAsm.Asm.Crypto.Quic.Kdf
import Libp2pAsm.Asm.Crypto.Quic.Number
import Libp2pAsm.Asm.Crypto.Quic.Packet
import Libp2pAsm.Asm.Crypto.Quic.Retry
import Libp2pAsm.Asm.Crypto.RSA.Api
import Libp2pAsm.Codegen.Assembly
import Libp2pAsm.Codegen.CodecProbe
import Libp2pAsm.Codegen.BufferProbe
import Libp2pAsm.Codegen.ClockProbe
import Libp2pAsm.Codegen.Protocols

open Libp2pAsm

private def usage : String :=
  "Usage: libp2p-asm-codegen (asm|hex) <routine>\n" ++
  "       libp2p-asm-codegen eval (add|min) <u64> <u64>\n" ++
  "       libp2p-asm-codegen eval-codec <routine> <value|hex> <capacity|length>\n" ++
  "       libp2p-asm-codegen eval-buffer <hex> <ref-offset> <slots> <write-flag>\n" ++
  "       libp2p-asm-codegen eval-clock <hex> <drift-ns> <sample-span-ns>\n" ++
  "Routines: add, min, quic-encode, quic-decode, uvarint-encode, uvarint-decode,\n" ++
  "          buffer-resolve, clock-check, sha256-compress, sha512-compress,\n" ++
  "          sha256, sha512, hmac-sha256, hkdf-extract, hkdf-expand, tls-label,\n" ++
  "          aes128-expand, aes128-block, aes128-hp, ghash, gcm-seal, gcm-open,\n" ++
  "          x25519-public, x25519-raw, x25519-shared, ed25519-public,\n" ++
  "          ed25519-sign, ed25519-verify, p256-public, p256-ecdh, p256-sign,\n" ++
  "          p256-verify, secp256k1-public, secp256k1-ecdh, secp256k1-sign,\n" ++
  "          secp256k1-verify, der-header, der-decode, protobuf-varint, public-key,\n" ++
  "          peer-id, time-decode, time-encode, quic-initial, quic-keys, quic-update,\n" ++
  "          quic-nonce, quic-number, quic-protect, quic-unprotect, quic-retry,\n" ++
  "          quic-retry-check, rsa-pkcs1-sha256, rsa-pss-rsae-sha256.\n" ++
  "Protocol leaves: " ++ String.intercalate ", " Codegen.protocolNames ++ "."

private def auxiliary (name : String) : Except String Rv64.SAsm.Stmt :=
  match name with
  | "protobuf-varint" => .ok Asm.Codec.ProtobufVarint.decode
  | "public-key" => Asm.Identity.PublicKey.decode
  | "peer-id" => .ok Asm.Identity.PublicKey.peerId
  | "time-decode" => .ok Asm.Identity.Time.decode
  | "time-encode" => .ok Asm.Identity.Time.encode
  | "quic-initial" => Asm.Crypto.Quic.Kdf.derive .initial
  | "quic-keys" => Asm.Crypto.Quic.Kdf.derive .keys
  | "quic-update" => Asm.Crypto.Quic.Kdf.derive .update
  | "quic-nonce" => .ok Asm.Crypto.Quic.nonce
  | "quic-number" => .ok Asm.Crypto.Quic.reconstruct
  | "quic-protect" => Asm.Crypto.Quic.Packet.protect
  | "quic-unprotect" => Asm.Crypto.Quic.Packet.unprotect
  | "quic-retry" => Asm.Crypto.Quic.Retry.generate
  | "quic-retry-check" => Asm.Crypto.Quic.Retry.check
  | "rsa-pkcs1-sha256" => Asm.Crypto.RSA.rsaPkcs1Sha256
  | "rsa-pss-rsae-sha256" => Asm.Crypto.RSA.rsaPssRsaeSha256
  | _ => match Codegen.protocolRoutine name with
    | some body => body
    | none => match Codegen.codecRoutine name with
      | some body => .ok body
      | none => .error "Unknown routine."

private def routine (name : String) : Except String Rv64.SAsm.Stmt :=
  match name with
  | "add" => .ok Asm.addWords
  | "min" => .ok Asm.minWords
  | "buffer-resolve" => .ok Asm.resolveBuffer
  | "clock-check" => .ok Asm.checkClock
  | "sha256-compress" => .ok Asm.Crypto.SHA256.compress
  | "sha512-compress" => .ok Asm.Crypto.SHA512.compress
  | "sha256" => .ok Asm.Crypto.SHA256.hash
  | "sha512" => .ok Asm.Crypto.SHA512.hash
  | "hmac-sha256" => Asm.Crypto.HMAC.sha256
  | "hkdf-extract" => Asm.Crypto.HKDF.extract
  | "hkdf-expand" => Asm.Crypto.HKDF.expand
  | "tls-label" => .ok Asm.Crypto.TlsKdf.encodeLabel
  | "aes128-expand" => .ok Asm.Crypto.AES.expand
  | "aes128-block" => .ok (Asm.Crypto.AES.encrypt false)
  | "aes128-hp" => .ok Asm.Crypto.AES.headerProtection
  | "ghash" => .ok Asm.Crypto.GCM.update
  | "gcm-seal" => .ok Asm.Crypto.GCM.seal
  | "gcm-open" => .ok Asm.Crypto.GCM.open
  | "x25519-public" => Asm.Crypto.Curve25519.X25519.publicKey
  | "x25519-raw" => Asm.Crypto.Curve25519.X25519.raw
  | "x25519-shared" => Asm.Crypto.Curve25519.X25519.sharedSecret
  | "ed25519-public" => Asm.Crypto.Curve25519.Ed25519.publicKey
  | "ed25519-sign" => Asm.Crypto.Curve25519.Ed25519.sign
  | "ed25519-verify" => Asm.Crypto.Curve25519.Verify.verify
  | "p256-public" => Asm.Crypto.Weierstrass.publicKey .p256
  | "p256-ecdh" => Asm.Crypto.Weierstrass.ecdh .p256
  | "p256-sign" => Asm.Crypto.Weierstrass.sign .p256
  | "p256-verify" => Asm.Crypto.Weierstrass.verify .p256
  | "secp256k1-public" => Asm.Crypto.Weierstrass.publicKey .secp256k1
  | "secp256k1-ecdh" => Asm.Crypto.Weierstrass.ecdh .secp256k1
  | "secp256k1-sign" => Asm.Crypto.Weierstrass.sign .secp256k1
  | "secp256k1-verify" => Asm.Crypto.Weierstrass.verify .secp256k1
  | "der-header" => .ok Asm.Codec.Der.encodeHeader
  | "der-decode" => .ok Asm.Codec.Der.decode
  | _ => auxiliary name

private def evalRoutine (name a b : String) : IO UInt32 := do
  unless name == "add" || name == "min" do return 2
  let .ok body := routine name | return 2
  let some lhs := Codegen.parseWord a | return 2
  let some rhs := Codegen.parseWord b | return 2
  let .ok code := body.lower | return 1
  let initial : Rv64.State := { pc := 0x10000 }
  let state := ((initial.setReg .x10 lhs).setReg .x11 rhs).setReg .x8 0x11223344
  let .ok done := Rv64.runUntil { base := 0x10000, code } 0 32 state | return 1
  let output := [done.state.getReg .x10, done.state.getReg .x11, done.state.getReg .x8]
  IO.println (Codegen.hexBytes (Codegen.wordBytes output))
  return 0

private def printProbe (result : Option ByteArray) : IO UInt32 := do
  let some bytes := result
    | (← IO.getStderr).putStrLn "Invalid probe input or execution."; return 2
  IO.println (Codegen.hexBytes bytes)
  return 0

private def emit (format name : String) : IO UInt32 := do
  let .ok body := routine name
    | (← IO.getStderr).putStrLn "Unknown routine or invalid routine layout."; return 2
  let .ok code := body.lower
    | (← IO.getStderr).putStrLn "Assembly layout validation failed."; return 1
  let .ok bytes := Rv64.encodeProgram code
    | (← IO.getStderr).putStrLn "Instruction encoding failed."; return 1
  match format with
  | "asm" => IO.print (Codegen.assembly code); return 0
  | "hex" => IO.println (Codegen.hexBytes bytes); return 0
  | _ => (← IO.getStderr).putStrLn usage; return 2

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--help"] => do IO.println usage; return 0
  | ["eval", name, a, b] => evalRoutine name a b
  | ["eval-codec", name, argument, limit] => printProbe (Codegen.evalCodec name argument limit)
  | ["eval-buffer", hex, offset, count, write] =>
    printProbe (Codegen.evalBuffer hex offset count write)
  | ["eval-clock", hex, drift, span] => printProbe (Codegen.evalClock hex drift span)
  | [format, name] => emit format name
  | _ => do (← IO.getStderr).putStrLn usage; return 2
