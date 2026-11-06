---
title: 実装・検証の台帳
last_updated: 2026-11-07
tags:
  - implementation
  - testing
  - formal-verification
---

# 実装・検証の台帳

## 完了判定

ゴールは[設計書](design.md)のM0〜M5全体である。
以下の部分実装だけで完了とはしない。未実装の機能に対する入口や成功を返すstubは設けない。
現時点のコードは研究・開発用であり、公開ネットワークへ接続する完成品ではない。

| 段階 | 実装・実行 | 形式的検証 | 残る作業 |
| --- | --- | --- | --- |
| M0 | 命令部分集合、領域メモリ、SAsm、エンコード、全33命令のQEMU照合、Limits検査、時計判定の仕様・ASM | レジスタ補題、flatten長、加算の実fetch、fetch/trace/frame/storeの論理、既定Limits、時計全入力のASM対応・所有権・上限 | Linux event ABI、資源制限の実強制、VC合成、ISA対応 |
| M1 | 2種類のvarintと領域参照を仕様・ASMで実装、正常／異常／境界を照合 | 全62／63ビット域の仕様往復、任意の適切な配置／戻り先・包含programにおける4 Codecとbuffer resolverの全入力ASM対応・ABI・メモリ・命令上限 | 登録・解放ライフサイクルの所有権 |
| M2a | SHA-256/SHA-512、HMAC/HKDF、TLS labelの独立仕様・ASM・公開ベクトルを統合 | SHA word演算14件、長さ・構成の補題12件、公理監査 | 全関数のASM対応・所有権・命令上限・定数時間性 |
| M2b | AES-128、GHASH、GCM、QUIC Initial／更新鍵・nonce・packet number・パケット保護・Retryの仕様・ASM | 全256 byteのS-box回路対応、counter・長さ・masked commit・nonce単射の補題 | 全関数の対応・所有権・上限・定数時間性 |
| M2c | X25519、Ed25519、P-256、secp256k1、DER header・証明書構造／時刻、PublicKey protobuf、canonical Peer ID、RSA署名検証の仕様・ASM | Curve25519・Weierstrassの算術／形式補題、protobuf uint64とDER header encode/decodeの全入力ASM対応・ABI・所有範囲・命令上限 | 全関数の対応・所有権・上限・定数時間性、証明書認証 |
| M3 | TLS鍵スケジュール／handshake codec、QUIC packet/frame/TP parser・builder・batch・permission、損失回復の20 APIをライブラリへ統合し再検査 | TLSの構成・境界・実命令断片、wire境界・frame permission、回復の算術・不変量補題18件 | 双方向QUIC/TLSの状態統合、輻輳タイマーの接続統合、障害注入 |
| M4 | stream受信／送信、multistream、Pingの20 leafをライブラリへ統合し再検査 | 算術・状態不変量とstream ordinal 16命令leafの対応 | 接続への統合、資源回収、全体refinement・資源・CT証明 |
| M5 | Go/Rust対向fixtureを固定し、fixture同士の認証・双方向Pingを16組で確認 | ASM核との対応は未成立 | Linux/RV64 ASM核との両方向実通信、台帳全体の監査 |

## レビュー予算の処理

設計レビューは3回で予算を消費した。最新指摘は設計書§12で解消または不採用し、その後の実装差分はパネル未レビューである。
応答なし・HTTP 500・タイムアウトのレビュアーは承認ではない。リポジトリにリモートがなく、作業はlocal-onlyのためGitHub PRは作成しない。未達は本台帳が記録する。

| 最新指摘 | 処理 |
| --- | --- |
| 切り詰めUDPの受信レート上限がない | 解消。§5.4で切り詰め・不正・認証失敗も受信窓へ計上し、飽和時は読み取りを抑制する |
| 壁時計の「許容外」が未定義 | 解消。`Limits.maxWallClockDriftNs` を有限必須とし、無限許容は禁止 |
| 長さ検査前の減算underflow | 解消。§5.3は `length ≤ capacity` 成功後だけ減算する |
| 2^64近傍の範囲検査overflow | 解消。同じ順序と、最終バイトが表現可能な非ラップ条件 |
| 送信トークン枯渇で永久停止 | 解消。§5.2は接続失敗、世代枯渇スロットの退役、空きなしの即時エラー |
| would-blockの予約が非有界 | 解消。`maxPendingSends`、`maxSendWaitNs`、`maxSendAttempts`。期限は延長しない |
| 壁時計異常で全接続を停止 | 解消。壁時計は処理中と新規認証、単調時計異常だけ全接続 |
| 未対応protocol IDの動作が不明 | 解消。§2・§8の長さ付き `na\n`。処理したふりはしない |
| チャンク分割で§6.2が見えない | 不採用。全文に定義があり、レビュー分割の制約 |
| ホストの乱数・送信結果・時刻を信頼 | 不採用。合意した環境契約であり、ホスト侵害への耐性は主張しない |
| 切り詰めUDPの有用部分も受け入れるべき | 不採用。欠損データは全体をdropし、損失回復はQUICが担う |
| AES-256-GCM、ChaCha20、X25519、P-384をMUSTとすべき | 不採用。RFC 8446 §9.1で前三者はSHOULD、P-384はMUSTではない |

予算消費後も残る実装上の未達は、接続状態機械、証明書認証の統合、資源カーネル、回復処理の接続統合、ASM核による相互運用、全体のrefinement・資源・定数時間性証明である。

## 並列作業員の状況

2026-11-07に証明書認証（feat/streams）と資源カーネル（feat/aead）の作業員がワークスペースのクレジット枯渇で停止した。
認証側はM0〜M1部分凍結（Auth／CertificateVerify／発行のEd25519経路が独立oracle・Spec・全snapshot・GNU・両QEMUで一致。完全な認証は22,765,419命令でquantum 2^24を超えるため、接続核の継続機構が必須）、カーネル側はM1部分凍結（Limits 758・registry・queue 86・request 144・init 16、GNU＋両QEMU。Requests cleanupは未検査）まで到達した。
クレジット回復まで本体で実装を継続する。部分凍結成果物は検証の経過記録であり、完了とは扱わない。

## 現行Codecの契約

- QUIC: RFC 9000 §16。1/2/4/8バイト、値は `0 ≤ n < 2^62`。
  最小幅で出力し、受信時は合法な非最小幅も受理する。
- multiformats: unsigned LEB128、最大9バイト、値は `0 ≤ n < 2^63`。
  非最小表現と9バイト目の継続を拒否する。
- encoder: `a0=value, a1=buffer, a2=capacity` →
  `a0=status, a1=written, a2=0`。失敗時は書き込まない。
- decoder: `a0=buffer, a1=length` →
  `a0=status, a1=value, a2=consumed`。失敗時のvalue/consumedは0。
- status: 0=成功、1=切断／出力容量不足、2=整数overflow、3=非最小unsigned varint。
- ポインタ・長さに対応する領域の所有権・権限は呼び出し側の前提であり、
  未検査の外部整数をこの内部leaf ABIのポインタとして渡してよいわけではない。
- モデルテストのfuel=512とは別に、実fetch／runUntilの普遍的対応定理がある。
  任意の適切なコード配置・戻り先で、QUIC encode/decodeは128/64命令、
  unsigned encode/decodeは160/128命令以内。成功／エラー、ABI保存、外国領域の保持、
  実行途中のstore範囲も含む。詳細は
  [証明契約](../Libp2pAsm/Refinement/AsmCodec/README.md) を参照する。
  包含programの実fetchに対応し、戻るまでleafの外へ出ない。戻り先はleaf外かつ整列済みとし、
  メモリ・コードの非ラップ／分離などの構造的前提を明示する。

## 領域参照の内部ABI

`Asm.resolveBuffer` はcore所有の登録表を参照する。登録表そのものをネットワークから受け取らない。
slotとreferenceはそれぞれ4つのLE64フィールドで、8バイト境界に配置する。
slotはgeneration/base/capacity/flags、referenceはslot/generation/offset/lengthである。
flagsのbit 0がactive、bit 1がwritable。それ以外のbitは不正として拒否する。
長さ検査に成功してから `capacity - length` を計算する。非空領域とone-past-endの
表現可能性を要求するため、空ビューのアドレスもwrapしない。

入口は `a0=table, a1=reference, a2=slot count, a3=write (0/1)`、
出口は `a0=status, a1=address, a2=length`。エラーは両結果を0にする。
statusは1=未知slot、2=失効、3=範囲外、4=不正登録情報、5=読み取り専用。
実際のmapping・寿命・コードとの分離は登録処理の前提であり、アドレスを解決しただけで
OSのmappingや所有権を作り出したという保証ではない。登録・解放のライフサイクルは未実装。

## 実行した検査

`README.md` の手順で再実行できる。

| 検査 | 現行の証拠 |
| --- | --- |
| `lake build` | 成功 |
| `lake exe libp2p-asm-tests` | レジスタ・メモリ・エンコーダ、RFC 9000ベクトル、幅境界、切断位置、varint差分・buffer guards |
| 公理監査 | `Tests/Axioms.lean` と `Refinement/Codec/Axioms.lean`。現行の依存はpropext、Quot.sound、Classical.choiceの範囲 |
| `tests/native/check.py` | 加算68＋最小値68ケースでモデル・独立計算・QEMUを照合 |
| `tests/native/codecs.py` | QUIC 539＋unsigned 662ケースで仕様・モデル・QEMU・guard bytesを照合 |
| `tests/native/buffers.py` | 285ケースで世代・権限・生ABIの不正flags・64ビット境界を照合 |
| `tests/native/isa.py` | 全33命令を693ケースで独立算術・モデル・GNU・QEMUと照合。保存レジスタとメモリguardも確認 |
| `tests/native/clocks.py` | 509ケースでsigned UTC・128-bit経過差・障害／回復を仕様・独立Python・GNU/QEMU・直接encode/QEMUと照合 |
| `Tests/AsmCrypto/check.py` | SHA圧縮85/63ケース、パディング済みhashlibメッセージ各17件、保存レジスタ・guard・消去を両QEMU経路で照合 |
| `Tests/HashCrypto/check.py` | 173ケース、最大HKDF出力8160バイト、TLS labelの7..255バイト制約、全snapshot・消去・失敗原子性を両QEMU経路で照合 |
| `Tests/Aead/check.py` | 160ケース。NIST・cryptography 49.0.0・仕様・実命令・両QEMU経路。失敗時出力保持、tag全byte、保存・消去・アクセス列 |
| `Tests/Curve25519/check.py` と追加2 suite | 196ケース、113トレース組、392 QEMU実行。別途RFC 7748の1,000回反復をSpec・cryptography・両QEMUで照合。全snapshot・消去・アクセス列 |
| `Tests/Der/check.py` | decode 400＋encode 144ケース、うち383をGo ASN.1とも照合。仕様・実命令・両QEMU、全snapshot・headerアクセス範囲 |
| `Tests/Identity/check.py` | protobuf uint64 35＋公開鍵129＋Peer ID 23ケース。125をgo-libp2pとも照合。仕様・実命令・両QEMU、全snapshot・消去・アクセス範囲 |
| `Tests/Weierstrass/check.py` と追加suite | 807ケース、54トレース組、1,614 QEMU実行。P-256／secp256k1の有限体・点・鍵交換・署名、全snapshot・消去・範囲 |
| `Tests/QuicCrypto/check.py` と追加suite | 541ケース、228トレース組、1,538 QEMU実行。RFC9001 A.1–A.4、鍵更新後の元HP鍵保持、全snapshot・消去・範囲 |
| `Tests/CertificateTime/check.py` | decode 297＋encode 229＋有効期間700ケース。Python datetime／Int・Lean Std/Nat仕様・実命令・両QEMU。アドレス上端は別途モデル2件 |
| `Tests/CertificateAlgorithms/check.py` | signature 1,251＋public-key 173ケース。構造的ASN.1仕様と独立したASM認識、GNU／両QEMU・全snapshot |
| `Tests/RSA/check.py` | 241ケース・482 QEMU実行、補助定理24件。PKCS1/PSS SHA256、独立Nat／Python pow／cryptography、全snapshot・消去・範囲 |
| `Tests/Certificate/check.py` | 1,067ケース・2,134 QEMU実行。リンク済みparserの命令位置6,732/7,916（85.04%）を実行。独立構造parser／datetime・Spec・実命令、全snapshot・アクセス・消去。暗号学的認証の検査ではない |
| `Tests/Tls/check.py` と `audit.py` | 本体で7,482ケース・59トレース組・15,082 QEMU実行。Go1.24.1 QUICConnとRFC8448の鍵スケジュール／handshake bytes、36補助定理。TLS FSMは含まない |
| `Tests/QuicWire/check.py` | 5,126ケース・10,252 QEMU実行。quic-go0.59.0と377 codecケース、全snapshot・範囲・消去、123定理の自動公理監査 |
| `Tests/Recovery/audit.py` | 308遷移・616 QEMU実行。18定理のkernel検査・公理監査。PN空間・ACK台帳・RTT/輻輳・パス単位の増幅制限。FSM統合は含まない |
| `Tests/Streams/check.py --native` | 5,469ケース・10,938 QEMU実行。独立Python・Spec・実命令、20 leafの全snapshot・範囲、239定理の自動公理監査。接続統合ではない |
| `Tests/Pipeline/check.py` | Initial鍵導出→unprotect→packet/frame parse→TLS decodeをleafの実lower命令列で連結。5段階1,088,869命令、独立Pythonモデルと全バッファ・スタック消去・保存レジスタ一致。FSM・認証判定は含まない |
| `Tests/ParserProof/Axioms.lean` | 587定理の推移的公理監査。protobuf decode 256、DER decode 129／header encode 157命令の普遍的上限・実fetch・ABI・所有範囲 |
| 公開codegen | 新規42 routineのlower/encodeを単体検査。7系列のCLI生成byteがQEMU検査済み成果物と完全一致 |
| 暗号の参照仕様 | SHA公開ベクトル22件、RFC 4231の7件、RFC 5869 A.1–A.3、追加709件のhashlib/hmac比較 |
| 生成バイト比較 | 各nativeケースでGNUの配置後 `.text.protocol` とLeanエンコーダの全バイトを比較 |
| `tests/interop/check_peers.py` | Go v0.51.0／Rust 0.57.1同士の16組。IPv4/IPv6、両identity・両役割、双方向3 Ping。ASM核の試験ではない |

テスト結果は全入力の形式証明ではない。証明書parser以外のカバレッジや、リポジトリ全体の80%達成は未測定である。
上に明示した定理の対象と、その前提を超えて一般化しない。
命令数・所有メモリの導出上限、定数時間性、相互運用、障害注入、レビューゲートは
未完了の項目として管理し、テスト成功だけで検証済みへ変更しない。
