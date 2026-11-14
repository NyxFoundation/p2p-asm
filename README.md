# p2p-asm

Lean 4で構造化アセンブリを定義し、RV64IMまたはLinux x86-64の命令列として
実行・検証するP2Pスタック実装を目指すプロジェクトです。Lean package namespaceと既存の
実行ファイル名は互換性のため当面 `Libp2pAsm` / `libp2p-asm-*` を維持します。
[evm-asm](https://github.com/Verified-zkEVM/evm-asm)の検証付きマクロアセンブラに
着想を得ています。RV64の命令・実行モデルとx86-64の命令・アセンブリ出力には
[LeanAsm](https://github.com/NyxFoundation/LeanAsm)を使用しています。
**zkVMを使用するプロジェクトではありません。**

## 現在の状態

実装中です。暗号、証明書構造、QUIC wire、TLS鍵スケジュール／handshake codec、
ストリーム再構成・送信、multistream・Pingの部品をASMで実装しています。
RV64版はQEMU、x86-64版はLinuxネイティブの実行テストで照合します。
varint、buffer resolver、時計判定、protobuf uint64、DER headerには全入力の対応証明があります
（所有権・配置などの前提は各契約を参照）。暗号・プロトコル全体の証明は未完成です。
**x86-64への変換は未証明です。既存のRV64証明はx86-64版には適用されません。**
**完成したQUIC/TLS接続、Peer ID認証、ASM核を使ったPing相互運用はまだありません。**

[実装・検証の台帳](docs/implementation-status.md)、[設計書](docs/design.md)、
[LeanAsmとの境界](docs/leanasm.md)、[移植元と信頼境界](docs/provenance.md)を参照してください。

## 開発時の実行

Lean/Elanを導入した環境で、固定した `lean-toolchain` を使用します。

```sh
lake build
lake exe libp2p-asm-tests
lake env lean Tests/Axioms.lean
lake exe libp2p-asm-codegen --help
lake exe libp2p-asm-codegen asm quic-decode
```

### Linux x86-64

GCCとGNU binutilsを導入したx86-64 Linuxで、CからQUIC varintをデコードします。
QEMUやSIMD・SHA拡張は不要です。

```sh
mkdir -p build/x64
lake exe libp2p-asm-codegen --target x86_64 asm quic-decode > build/x64/quic-decode.S
gcc -Wall -Wextra -Werror -fPIE -pie -Iinclude Examples/X64.c build/x64/quic-decode.S -o build/x64/example
build/x64/example
python3 Tests/X64/check.py
```

正常終了が成功です。C入口はSystem V AMD64 ABIの
`protocol_entry(struct p2p_asm_registers *)` で、既存ルーチンの引数・戻り値を
レジスタ配列で渡します。呼出側がバッファと必要なスタックを確保します。
全生成対象が選択可能ですが、`hex`出力はRV64専用です。
[ABI・制約・検証範囲](docs/x86-64.md)を参照してください。

### RISC-V RV64IM（デフォルト）

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
実行環境はLinux/RV64とLinux/x86-64です。RV64の開発・検証にはQEMUも利用します。

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
