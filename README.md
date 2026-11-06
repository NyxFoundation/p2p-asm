# libp2p-asm

Lean 4で構造化アセンブリを定義し、RV64IM命令列として実行・検証する
libp2p実装を目指すプロジェクトです。
[evm-asm](https://github.com/Verified-zkEVM/evm-asm)の検証付きマクロアセンブラに
着想を得ています。**zkVMを使用するプロジェクトではありません。**

## 現在の状態

実装中です。暗号、証明書構造、QUIC wire、TLS鍵スケジュール／handshake codec、
ストリーム再構成・送信、multistream・Pingの部品をASMで実装し、生成命令をQEMUで照合しています。
varint、buffer resolver、時計判定、protobuf uint64、DER headerには全入力の対応証明があります
（所有権・配置などの前提は各契約を参照）。暗号・プロトコル全体の証明は未完成です。
**完成したQUIC/TLS接続、Peer ID認証、ASM核を使ったPing相互運用はまだありません。**

[実装・検証の台帳](docs/implementation-status.md)、[設計書](docs/design.md)、
[移植元と信頼境界](docs/provenance.md)を参照してください。

## 開発時の実行

Lean/Elanを導入した環境で、固定した `lean-toolchain` を使用します。

```sh
lake build
lake exe libp2p-asm-tests
lake env lean Tests/Axioms.lean
lake exe libp2p-asm-codegen --help
lake exe libp2p-asm-codegen asm quic-decode
```

生成したRV64コードを実行するテストにはPython 3、GNU RISC-V binutils、
Linux user-modeの `qemu-riscv64` が必要です。Debian/Ubuntuでは通常
`binutils-riscv64-unknown-elf` と `qemu-user` が該当します。

```sh
python3 tests/native/check.py
python3 tests/native/codecs.py
python3 tests/native/buffers.py
python3 tests/native/isa.py
python3 tests/native/clocks.py
python3 Tests/Crypto/differential.py
python3 Tests/AsmCrypto/check.py
python3 Tests/HashCrypto/check.py
# AEAD比較にはTests/Aead/requirements.txtのtest-only依存も必要
python3 Tests/Aead/check.py
# Curve25519比較のtest-only依存はTests/Curve25519/requirements.txt
python3 Tests/Curve25519/check.py --jobs 3
python3 Tests/Der/check.py
python3 Tests/Identity/check.py
python3 Tests/CertificateTime/check.py
python3 Tests/Weierstrass/check.py
python3 Tests/QuicCrypto/check.py
python3 Tests/CertificateAlgorithms/check.py
python3 Tests/Certificate/check.py
python3 Tests/QuicWire/check.py
python3 Tests/QuicWire/oracle.py
python3 Tests/QuicWire/audit.py
python3 Tests/Recovery/audit.py
python3 Tests/Streams/check.py --native
python3 Tests/Pipeline/check.py
# TLS・RSAの全検査は各READMEの再現手順を参照
```

ツール名が異なる場合は `--prefix riscv64-linux-gnu-`、QEMUの場所が異なる場合は
`--qemu /path/to/qemu-riscv64` を各テストへ渡します。生成物はgitignore対象の `build/` または `Tests/Tls/.build/` に置かれます。
暗号のABI・容量・検証範囲は [SHA圧縮](Tests/AsmCrypto/README.md) と
[hash/HMAC/HKDF](Tests/HashCrypto/README.md)、[AES/GCM](Tests/Aead/README.md)、
[Curve25519](Tests/Curve25519/README.md)、[DER](Tests/Der/README.md)、
[公開鍵とPeer ID](Tests/Identity/README.md)、[証明書時刻](Tests/CertificateTime/README.md)、
[Weierstrass曲線](Tests/Weierstrass/README.md)、[QUIC暗号](Tests/QuicCrypto/README.md)、
[RSA](Tests/RSA/README.md)、[証明書パーサー](Tests/Certificate/README.md)、
[TLS部品](Tests/Tls/README.md)、[QUIC wire](Tests/QuicWire/README.md)、
[stream/multistream/Ping](Tests/Streams/README.md)、[損失回復](Tests/Recovery/README.md)、
[ASM核連結](Tests/Pipeline/README.md)、資源設定は
[Limitsと時計](docs/limits-and-clock.md) を参照してください。
これは単体テスト用の実行経路で、ネットワークサーバーの起動手順ではありません。

## 開発目標

- Lean 4の実行可能なプロトコル仕様と、構造化ASMによる実装を用意する。
- ASMから生成するRV64IM命令列と仕様の対応を証明する。
- QUIC v1、TLS 1.3、libp2pのPeer ID認証、暗号プリミティブをASMで実装する。
- UDP・時計・乱数などの環境依存を分離し、実通信と決定的シミュレーションを行う。
- `evm-asm`の汎用基盤を選択的に再利用し、変更に影響される証明を再検証する。

「ASM」は独自の抽象的なネットワーク命令だけを実行する機械ではありません。
最終的なプロトコル核は実CPUの命令列です。
通常の実行環境はLinux/RV64を基準とし、開発・検証にはQEMUも利用する方針です。

## 最初の相互運用目標

既存libp2p実装に対し、接続開始・受け入れの両方向で次を実証します。

```text
UDP → QUIC/TLS → Peer ID認証 → QUIC双方向ストリーム
    → multistream-select → /ipfs/ping/1.0.0 の32バイト往復
```

損失、並べ替え、重複、タイムアウト、不正入力も検証対象です。
QUICのPINGフレームやEthereumのReq/Resp Pingとは別のプロトコルです。

## 対象範囲

Ethereumコンセンサス層で利用されるQUICの通信フローを出発点とします。
初期段階にはEthereum固有のReq/Resp、Gossipsub、discv5、TCPを含めません。

参照したEthereum仕様ではQUICが主トランスポートですが、TCP対応も必須です。
したがって、この初期目標の達成だけでEthereumのP2P仕様への完全準拠や、
汎用libp2pスタック全体の完成を主張しません。
