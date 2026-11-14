---
title: 移植元と信頼境界
last_updated: 2026-11-07
tags:
  - provenance
  - licensing
  - formal-verification
---

# 移植元と信頼境界

## 基点と依存閉包

- evm-asm: `7e65e4d024718f704226cd795f3d03d4e9aafe13`。
- riscv-zkvm: `afcbc45e1c74c2d296e032b5606dd977a304e8ad`。
- 実装のビルド依存: Lean `v4.33.0`、同梱の `Std`、および
  `NyxFoundation/LeanAsm`（`lakefile.toml`でcommit固定）。
  Mathlib、evm-asm、riscv-zkvmパッケージを直接importする依存はない。
- 調査元リポジトリは変更していない。ライセンスは
  [evm-asm](../LICENSES/evm-asm.txt)と[riscv-zkvm](../LICENSES/riscv-zkvm.txt)に保存する。

| 移植先 | 参照元 | 採用範囲 |
| --- | --- | --- |
| `Rv64/Vocabulary.lean` | `LeanAsm/Rv64/Basic.lean` | 共通Word、レジスタ、trap |
| `Rv64/Profile.lean` | p2p-asm固有 | 証明対象を限定する有限命令profileとLeanAsmへの全域embedding |
| `Rv64/Basic.lean` | compatibility umbrella | 既存importを維持する薄い入口。命令型は `Profile.lean` の共有型別名 |
| `Rv64/Memory.lean`, `State.lean`, `Execution.lean`, `Encoding.lean` | `LeanAsm/Rv64/*` | region memory、状態、RV64意味論、machine-code encoder |
| `Rv64/SAsm.lean` | `EvmAsm/Rv64/SAsm/Ast.lean`, `Flatten.lean` | 構造化分岐・ループと命令数に基づく相対offset。`LowerRv64`/`EmitAsm`を介してLeanAsmへ接続 |
| `Asm/Crypto/AES/Circuit.lean` | BearSSL `aes_ct64.c`、`7561e7d6c86171257a4153d95202b0791b3612a8` | Boyar–Peraltaの115 gate S-box回路。MIT表記は [bearssl.txt](../LICENSES/bearssl.txt) |
| `Crypto/Curve25519/` | HACL* `f557259007db9933442dde10aa995c1b00bd3446`、RFC 7748/8032 | 5×51 limb、Montgomery ladder、complete Edwards式のRV64実装。独立Nat仕様。詳細な差分・ライセンス・blob固定は [台帳](../Tests/Curve25519/provenance.json) |
| `Crypto/Weierstrass/` | HACL* `f557259007db9933442dde10aa995c1b00bd3446`、SEC2 | P-256／secp256k1の独立Nat仕様とcomplete homogeneous式のRV64。詳細な採用範囲は [曲線台帳](../Tests/Weierstrass/README.md) |
| `Crypto/RSA/` | HACL* `f557259007db9933442dde10aa995c1b00bd3446`、RFC8017 | 公開署名検証のMontgomery／EMSA実装。私有演算は提供しない。原コード・ベクトル・ライセンスは [RSA台帳](../Tests/RSA/README.md) |
| `Spec/Identity/Time.lean` | Lean同梱 `Std.Time.PlainDate`、RFC5280 | Spec encoderの暦変換にStdを利用。ASMは独立した整数演算で、ホスト時刻変換を呼ばない |
| `Identity/X509/` | X.690、RFC5280/4055/5480/5758/8410、libp2p TLS binding | 独立構造仕様・RV64 parser。cryptography49.0.0の署名証明書はtest-onlyで、ASN.1／cryptoをruntimeへリンクしない |
| `Quic/Wire/` | RFC9000/9001、quic-go0.59.0のwire codec | 独立仕様・RV64。Go codec比較はtest-only。[RFC表記](../LICENSES/Quic-Wire-RFC.txt)・[quic-go表記](../LICENSES/Quic-Wire-quic-go.txt)を保持 |
| `Tls/` | RFC8446/8448/9001、Go1.24.1 `crypto/tls.QUICConn` | handshake codec・SHA256鍵スケジュール。Goは独立oracleのみでruntime TLSには使わない。[RFC表記](../LICENSES/Tls-RFC.txt)を保持 |
| その他の現行モジュール | RISC-Vと各プロトコルの規範仕様 | このリポジトリで記述したモデル・実装・テスト |

BearSSLの回路は型付きRV64命令へ展開し、Cライブラリへはリンクしない。
AESの独立仕様はGF(2^8)の逆元とaffine変換で記述し、全256 byteについて
回路との一致をLeanで検査する。gateのメモリ実装・転置・AES全体の対応証明は別である。
元パッケージのファイル全体や証明を移植したという意味ではない。
Sail生成モデルのソースはまだ取り込んでいないため、そのBSD-2-Clauseライセンスを
現行コードのライセンスとして流用しない。将来取り込む場合はファイルごとに保持する。

## 変更した意味論

zkVMのアドレス範囲、専用ECALL、アクセラレータは使わない。
メモリは有限の領域配列とし、各領域の非空性、64ビットアドレス範囲、
領域間の非重複、書き込み権限を検査する。アクセス開始位置だけでなく、
全バイト範囲と命令幅のアラインメントを検査する。
現行モデルは領域登録のaliasを許さない。同じ領域内の読み取り専用ビューとは区別する。

コードは別の不変命令列で表し、プログラムの配置・アラインメント・アドレス範囲と、
書き込み可能データ領域との非重複を検査する。
これはOSのメモリ保護を形式検証したものではない。

命令部分集合は `Rv64/Basic.lean` の `Instr` で明示する。
型にない命令を実行したふりはしない。
RV64IMの全命令、例外機構、特権命令、Linux自体をモデル化したという主張はしない。

## 再検査した主張と残る信頼

`Refinement/Registers.lean` と `Refinement/Arithmetic.lean` の定理は、
変更後のモデルに対してLeanカーネルで検査する。
上流のSail対応定理やHoare tripleを、こちらのモデルへ自動的に継承したとはしない。
加算には命令列実行の定理に加えて、`0x10000` に配置したプログラムがfetchを含めて
厳密に2命令で返る定理がある。任意オペランド・有効メモリに対する主張だが、
全関数・ISA・エンコード／リンク後の生成物へ自動的に拡張したものではない。

現行の実行証拠は、同じASTからの命令列をLeanエンコーダとGNU assembler/linkerで比較し、
QEMUで実行して仕様／モデルと照合したテストである。
エンコーダ、GNUツール、QEMUの正しさをLeanで証明したという意味ではない。
Leanカーネル、未検証の生成物ツール、ISA対応、OS・ハードウェアは信頼境界に残る。
暗号・環境乱数・時計・鍵保護の保証は、現時点ではまだ成立していない。
