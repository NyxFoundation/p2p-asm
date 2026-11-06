---
title: libp2p-asm 設計
last_updated: 2026-11-06
tags:
  - design
  - lean4
  - rv64im
  - libp2p
  - quic
  - formal-verification
---

# libp2p-asm 設計

## 1. 状態と合意事項

本書は初期設計であり、実装済み機能や成立済みの定理を記述するものではない。
設計合意時には実装・ビルド設定・テストはなかった。その後、ユーザーの承認を受けて
M0〜M5の実装へ移行した。現在の成果と未達項目は[実装台帳](implementation-status.md)で管理する。
以下のアーキテクチャ、API名、受け入れ条件は引き続き実装方針である。

ユーザーと合意した境界は次のとおり。

| 項目 | 方針 |
| --- | --- |
| ASMの意味 | Lean 4で構造化ASMを定義し、RV64IM命令列まで実行・検証する |
| QUIC | 既存ライブラリに丸投げせず、プロトコル自体をASMで実装する |
| TLS・暗号 | TLS 1.3、Peer ID認証、暗号プリミティブまで最終的なASM検証対象とする |
| 実行形態 | 通常のネットワーク実装。zkVM、ZK証明、zkVM向けABIは対象外 |
| 初期相互運用 | 既存libp2p実装との接続・認証・ストリーム選択・Ping往復 |
| 基盤再利用 | evm-asmの汎用部分を選択移植し、意味論変更の影響を受ける証明を再検証する |
| 設計合意時の成果物 | 設計文書のみ。後続の実装承認によってM0〜M5へ移行。上流リポジトリは変更しない |

## 2. 範囲と準拠の扱い

初期の通信プロファイルはQUIC v1とlibp2p Pingである。
接続開始側と受け入れ側の双方を実装する。ピアのアドレスと期待するPeer IDは
初期設定から与え、発見プロトコルを前提としない。

初回相互運用に含めないもの:

- TCP、Noise、Yamux/Mplexなどの別トランスポート経路。
- EthereumのStatus/Ping/Metadata、SSZ/Snappy、Gossipsub、discv5/ENR。
- Kademlia、Identify、リレー、AutoNAT、ホールパンチなどの上位機能。
- QUIC draft-29/v2、0-RTT、セッション再開、HTTP/3、QUIC DATAGRAM拡張。
- 自発的な接続マイグレーション、複数パスの同時利用。
- 性能目標値や、プロトコル全体の暗号学的安全性が既に証明されたという主張。

未対応のlibp2p protocol IDへの交渉には、§8の長さ付き `na\n` で応答し、
処理したふりをしない。未対応のプロトコルを広告・選択しない。
任意機能を使わないことと、相手から届く必須メッセージを処理しなくてよいことは別である。
特に0-RTT拒否、HelloRetryRequest、Retry、鍵更新、NAT rebindingなどの扱いは
後述の仕様台帳に含める。

[参照したEthereumコンセンサス仕様][ethereum-p2p]はQUICを主トランスポートとし、
QUICとTCPの両方のdial/listenを必須とする。QUICだけの本マイルストーンは
Ethereum P2P完全準拠ではない。実行層のdevp2p/RLPxも本書の対象ではない。

## 3. evm-asmから何を継承するか

### 3.1 調査基点

ローカルで確認したevm-asmのリビジョンは
`7e65e4d024718f704226cd795f3d03d4e9aafe13`。
そのLake設定はLean `v4.33.0`、Mathlib `v4.33.0`、
`riscv-zkvm v0.3.0`を参照していた。
これらは調査元のバージョンであり、本プロジェクトのビルド設定ではない。

| 確認した実コード | 採用する考え方 |
| --- | --- |
| [SAsm/Ast.lean][sasm-ast] | 生の命令ブロックを、分岐・ループ・呼び出しで構造化する |
| [SAsm/Flatten.lean][sasm-flatten] | 命令列と分岐オフセットを同じASTから導出する |
| [SAsm/Fn.lean][sasm-fn] | 関数本体と事前・事後条件を対応させ、VCから有界Hoare tripleを証明する |
| [SAsm設計][sasm-design] | 分離論理によるメモリ所有権と、名前付き検証条件による合成 |
| [Rv64/Basic.lean][evm-basic] | 現行RV64モデルは別パッケージへの再エクスポートである |

`Fn.Spec`は、flatten後のプログラムに対する
`cpsTripleWithin`を述べる。Leanの高水準関数を普通にコンパイルしただけで
この証明の代わりにはならない。
また、SAsmのループfuelは証明用であり、flattenされたコードに
自動で実行時のfuelカウンタが入るわけではない。入力・反復数の制限には、
実際のASMの検査とその証明が必要になる。

### 3.2 そのまま持ち込まない前提

参照元READMEには実験段階・仕様適合未検証という警告がある。
一方、現行の依存コードには[Sailとの対応証明][riscv-validation]がある。
READMEの警告だけを根拠に「証明がない」とは判断せず、
各定理の対象、前提、生成物への接続を個別に調べる。

依存パッケージの調査リビジョンは
`afcbc45e1c74c2d296e032b5606dd977a304e8ad`。
[Word.lean][riscv-word]にはzkVM固有のメモリ範囲があり、
アクセスの開始アドレスだけを検査するという既知の制約も明記されている。
[validation.md][riscv-validation]にはデコードのSail対応、
実行器と論理モデルの対応などの未証明部分が記録されている。

したがって、EVM本体、zkVMのメモリマップ・ECALL・アクセラレータ、
ゲスト用Codegen、進捗ダッシュボードは移植しない。
命令・ビット演算、分離論理、SAsm、VC生成器を候補として依存閉包を調べる。
SAsmの一括importはEVM向け補助モジュールも含むため、そのまま取り込まない。

移植は機能単位で行い、原リビジョン、ファイル、ライセンス、
変更した意味論、再成立させた定理を記録する。
evm-asmのMIT表記、生成SailモデルのBSD-2-Clause表記、
外部ランタイムなどのライセンスはファイル単位で確認・保持する。
既存の証明を、異なるメモリモデルの証明として読み替えない。

## 4. アーキテクチャ

### 4.1 二つの記述と一つの実装

- **Spec**: RFC/libp2p仕様に沿う、実行可能で純粋なLeanの参照意味論。
- **Asm**: レジスタ・メモリ・制御フローを明示するSAsmの実装。
- **Refinement**: Specの状態とASMのメモリ表現、入出力の対応を証明する。

```text
RFC / libp2p specifications
           |
           v
       Spec.step <-------- refinement -------- Asm.step
           |                                    |
   deterministic tests                      SAsm lowering
                                                |
                                         RV64IM instructions
                                                |
                                     encoding / linking checks
                                                |
                                          executable core
                                                ^
                                                | event / action ABI
                                                v
                                     Linux UDP / clock / entropy
```

ASMをプログラムの唯一の実装ソースとする。
シミュレータ用と本番用の独立したプロトコル実装や、
別管理のASM文字列を作って一致を期待する構成にはしない。
Specのテストとは別に、生成命令列の実行結果も比較する。

### 4.2 提案するモジュール境界

| モジュール境界 | 責務 |
| --- | --- |
| `Libp2pAsm/Spec/` | Codec、Crypto、TLS、QUIC、Identity、Multistream、Pingの意味論 |
| `Libp2pAsm/Rv64/` | 選択移植する機械モデル、メモリ権限、プログラム論理、SAsm |
| `Libp2pAsm/Asm/` | バイト処理からプロトコル遷移までのASM実装 |
| `Libp2pAsm/Refinement/` | 表現関係、関数契約、遷移・トレース対応、資源上限 |
| `Libp2pAsm/Codegen/` | エンコード、配置、生成物検査。ネットワーク処理は持たない |
| `runtime/` | 通常のLinux向けホストアダプタ。UDP・時計・乱数・鍵ロード |
| `tests/` | 仕様ベクトル、ASM差分実行、障害注入、既存実装との相互運用 |

SpecはAsm・Codegen・ホストI/Oに依存しない。
Asmのプログラム定義はCodegenに依存せず、仕様や証明注釈を参照できる。
Codegenからプロトコル仕様を変更しない。

通常の実行基準はLinux/RV64、開発環境は実機またはQEMUとする。
薄いホストアダプタのコンパイラは信頼境界に残る。
プロトコル核の正しさを、そのコンパイラに依存させない構成を目指す。
最初は単一イベントループが状態を所有し、共有可変状態とスレッド間競合を避ける。

## 5. 決定的なイベント駆動とホスト境界

意味論の形は `step(Config, State, Event) → StepResult` とする。
`StepResult`は更新後の状態と有限個のActionを含む。
1回のstep呼び出しを1 quantumと定義する。大きな外部Eventの処理は継続Eventへ
分割できるため、外部Eventとquantumは必ずしも1対1ではない。
Action数と命令数は同じquantumに対する独立した制限である。
これはAPIの設計表記であり、実装済みのLean宣言ではない。

### 5.1 入出力

| 入力Event | 必要な情報 |
| --- | --- |
| `ReceiveDatagram` | ソケット、送受信アドレス、受信時刻、UDPペイロード、切り詰めの有無 |
| `TimerExpired` | タイマーID・世代、単調時刻 |
| `ApplicationRequest` | Dial、OpenStream、Write、Finish、Reset、Closeと各ハンドル |
| `EntropyReady` | 要求IDと要求長に一致する乱数。失敗も明示する |
| `SendResult` | 送信トークン、OSへの投入成功時刻／would-block／失敗 |
| `ClockSample` | 単調時刻と証明書有効期間を判定する壁時計のサンプル |

Actionは `SendDatagram`、タイマー設定・取消、乱数・時計要求、
接続／ストリーム通知、アプリケーションへのバイト配送、処理継続要求を含む。
外部応答待ちは継続状態として保持し、応答ID・長さ・世代を照合する。
失効したタイマーや重複した外部応答を二重適用しない。
`EntropyReady`や`SendResult`はホストアダプタからの完了通知専用で、
ネットワークのバイト列から直接生成できるEventにはしない。

切り詰められた受信データグラムは、Initialを含む場合も全体をdropする。
完全に見える先頭パケットだけを処理したり、続きを別のUDP受信から補ったりしない。
接続・packet number・ストリームの状態を進めず、未認証の切り詰め入力だけで
既存接続をcloseしない。非切り詰めパケットの重複処理は§6.2の規則に従う。

タイムアウト計算には単調時刻、X.509のNotBefore/NotAfterには信頼できる
壁時計を使う。単調時刻だけでは暦上の証明書有効期間を判定できない。
壁時計と単調時刻の対応を保持し、巻き戻り・許容外のジャンプ・時刻取得失敗を
検出した場合は新たな認証を停止する。壁時計への信頼を失ったときは処理中の
ハンドシェイクも中止し、一時鍵・保留フレーム・関連タイマーを解放する。
信頼できる時刻の回復後に新しいハンドシェイクを開始し、有効期間検査を省略しない。
壁時計異常だけでは、既に認証を完了した接続を一律に停止しない。
壁時計の経過量と単調時計の経過量の差を、有限の64ビット設定値
`Limits.maxWallClockDriftNs` と比較する。上限未設定・無限許容は認めず、
M0で採用する時刻源の精度に基づいて値を決める。差の計算にもoverflowを許さない。
単調時計が不正なら損失回復や資源の期限も信用できないため、全接続をローカルで
停止・解放する。最初の時刻の正しさや悪意あるOSまで、この整合性検査で
保証するわけではなく、過去に配送したデータを取り消せるという主張もしない。

乱数はテスト時には固定イベント列、本番ではOSの暗号学的乱数源から取得する。
要求には期限を付け、取得失敗・長さ不一致・期限切れでは依存する処理を中止し、
保持した一時鍵を破棄する。弱いPRNG、固定値、以前の乱数へのfallbackは設けない。
短い応答列だけから乱数のエントロピー品質を証明することもできない。
再起動をまたぐ乱数品質、時計の妥当性、鍵の供給・保護は環境契約である。

### 5.2 送信結果の契約

`SendDatagram`を出しただけでは送信成功としない。
送信トークンは接続スロット・接続世代・送信試行番号の組とし、各要素を64ビットで
表す。同じ接続で試行番号を再利用せず、スロット再利用時には世代を進める。
カウンタをwrapさせない。試行番号の枯渇時は該当接続をローカルエラーで終了し、
保留I/Oを停止・回収する。世代が枯渇したスロットは再利用せず退役させる。
空きスロットがない新規要求には即座に資源エラーを返し、発行可能になるまで無期限に待たない。
ホストはその試行を終えた結果を1回通知し、核は保留表の組全体と照合する。
この照合は誤対応を防ぐが、悪意あるホストが送信成功を偽らないという証明ではない。
送信バッファを結果通知まで有効に保ち、OS投入成功を配送成功とはみなさない。

| `SendResult` | 状態遷移 |
| --- | --- |
| 成功 | OS投入時刻で送信履歴・bytes in flight・回復タイマーを更新し、試行の予約とバッファ貸与を解放する |
| would-block | 未送信として予約量を保持し、書き込み可能通知後に同一の不変データグラムを新しい試行トークンで再投入する。busy loopはしない |
| message-too-large | 未送信の試行を解放し、path MTUを更新する。必要なフレームは新packet numberで再構築し、最小サイズを維持できないpathは失敗させる |
| その他の回復不能な失敗 | 試行を解放し、該当path／接続を失敗させて上位へ通知する。他の接続を巻き込まない |

would-blockや失敗の通知後に、その試行をホストが遅れて送信してはならない。
結果不明の試行は未送信と決めつけて再投入せず、ホスト契約違反として停止する。
最初の試行時に `Limits.maxSendWaitNs` 後の期限と
`Limits.maxSendAttempts` を設定し、would-blockで期限を延長しない。
書き込み可能通知が一度も来なくても独立したタイマーで期限を処理し、
期限到達時には保留データを解放して失敗を通知する。
予約済みpacket numberを別パケットや別内容に再利用しない。

送信待ちも `Limits.maxPendingSends` に数え、満杯なら新しいアプリ書き込みへ
backpressureを返す。実送信量と予約量を区別して輻輳・増幅制限を守る。
タイマー処理より遅れて届く結果や、複数試行の順不同の結果はトークンで対応付ける。
接続世代が失効した結果は論理状態へ適用せず、残っている貸与資源だけを回収する。

### 5.3 バッファ所有権とABI

外部ポインタをLeanの参照や無制限リストとして扱わない。
論理モデルでは領域をbase・capacity・権限で表し、分離論理で所有権を管理する。
ABIのバッファ参照は領域ID・世代・offset・lengthとし、ホストが登録した領域内でのみ
アドレスへ解決する。パケット内の整数をホストポインタとして解釈しない。

最初に `length ≤ capacity` を検査し、失敗したらその場で返る。
成功した分岐でのみ `capacity - length` を計算し、`offset ≤ capacity - length` を検査する。
減算を先行評価したり、overflow未確認の `offset + length` に置き換えたりしない。
領域全体が64ビットアドレス空間からはみ出さないことも要求し、
その後のbase加算、命令幅の全バイト範囲、アラインメントを検査／証明する。
書き込み領域同士とコード領域の重なりを禁じ、読み取り専用aliasは契約で区別する。
コード領域は書き込み不能とし、ホストからプロトコル状態を直接書き換えない。

受信バッファはstep中の読み取り専用貸与とする。返却後も必要なデータは
核が所有する有界領域へコピーし、外部ポインタを継続へ持ち越さない。
送信バッファは結果待ちの間不変とし、ホストと核が同時に書き込まない。
解放と世代更新を対応させ、失効ハンドルの使用と二重解放を拒否する。

### 5.4 容量・DoS制限・非同期I/O

`Limits`を全上限の唯一の設定元とし、listen前に整合性を検証する。
M0（§10の基盤移植段階）で有限のデフォルト値と根拠を設定し、
各テストは使用した設定を記録する。数値はアリーナ容量と命令上限を踏まえた
M0の成果物であり、現時点で動く設定があるという意味ではない。
値はRFCの規定値とローカル方針を区別し、次の項目を省略可能にしない。

| 制限の組 | 対象 |
| --- | --- |
| 接続・ハンドシェイク | 全体／送信元別の同時数、開始レート、処理期限 |
| 受信レート | `rxWindowNs`内の`maxRxDatagrams`と`maxRxBytes`、1回の受信処理の`maxRxBatch` |
| パケット | UDP受信長、復号前後の領域長、packet/frame処理量 |
| ストリーム | 同時数、受信／送信buffer、CRYPTO再構成、ACK範囲数 |
| 入力・出力 | 入力Eventキュー、未送信データグラム、1 stepのAction数 |
| 外部要求 | `maxTimers`、`maxEntropyRequests`、`maxClockRequests`、`maxPendingSends`と各要求の期限 |
| 実行 | 1 quantumの命令数、処理継続の保留数、接続別のCPU予算（設定した単調時間窓あたりのASM命令数） |

ピアに広告するtransport parameterは、実際の容量と一致させる。
パケットサイズ上限はInitialの1200バイト要件を満たす。
AES-GCMではAEADへ渡す暗号文長が16バイトのtag長以上であることを先に確認し、
`plaintextLength = ciphertextLength - 16` が出力領域容量以下であることを検査する。
認証失敗時の一時的な復号内容を外へ配送しない。他のAEADも固有の出力長契約に従う。
安価な長さ検査と入場制限を、接続割当てや署名検証より先に適用する。
上限超過時のdrop、backpressure、reset、closeは仕様に従って区別する。
ネットワーク入力とアプリ要求で、結果通知・期限処理用の予約枠を消費し尽くさない。
切り詰め・不正・認証失敗のデータグラムも受信レートへ計上する。
予算を使い切った受信ソケットは読み取りを一時抑制し、期限・完了・他の接続の処理へ
制御を返す。dropのたびにログを生成せず、有界の集計値にする。
このユーザー空間の上限は、OS／回線全体のflood耐性や配送保証を意味しない。

非同期OS I/Oのコールバックは、上限付きキューへ完了Eventを渡すだけとする。
状態更新とAction発行は単一所有者が直列化する。要求を発行する前に完了枠を予約し、
キュー飽和時にも送信結果や資源解放通知を捨てない。
新たなUDP入力はdrop、アプリ要求はbackpressureとし、タイマーはID・世代別に集約する。

ネットワーク全体の終了ではなく、各イベント／処理quantumの有界実行を証明する。
大きな処理は明示的に継続へ分割し、公平なスケジューリングを仮定として記録する。
永久的な損失下での配送や、無条件の接続成功は保証しない。

## 6. 初期QUIC/libp2pプロファイル

| 項目 | 設計基準 |
| --- | --- |
| QUIC | RFC 9000のv1、RFC 9001のTLS統合、RFC 9002の損失回復・NewReno系輻輳制御 |
| アドレス | IPv4/IPv6とUDP、`/quic-v1`。接続開始時には期待するPeer IDも渡す |
| ALPN | `libp2p` |
| TLS | TLS 1.3、相互の証明書認証。QUICのCRYPTOフレームで運ぶ |
| ストリーム | QUICの双方向ストリームをlibp2pストリームとして利用 |
| プロトコル選択 | `/multistream/1.0.0`、完全一致で選択 |
| アプリケーション | `/ipfs/ping/1.0.0`、32バイトのエコー |

QUICには暗号化と多重化が組み込まれている。
接続に対するNoise、`/tls/1.0.0`の追加交渉、Yamux/Mplexは行わない。
ただし、各アプリケーションストリーム上のmultistream-selectは必要である。
TLSレコード層やTLS KeyUpdateをQUICへそのまま持ち込まない。
鍵更新にはQUICのkey phaseを用いる。

### 6.1 正常系の流れ

1. 接続開始側がアドレス・Peer ID・資源上限を検証し、CIDと鍵素材を用意する。
2. ClientHelloをCRYPTOで運ぶInitialを送る。Initialを含むデータグラムの
   UDPペイロード全体が少なくとも1200バイトになるよう必要分だけpaddingする。
   固定で1200バイトを追加するわけではない。Initial鍵導出と増幅制限も適用する。
3. 受け入れ側がInitialを処理し、TLS応答・証明書・クライアント認証要求を送る。
   CRYPTOは分割・並べ替え・再送を考慮して暗号化レベルごとに再構成する。
4. 両側がTLS transcript、CertificateVerify、Finishedとlibp2pの認証を検証する。
   接続開始側は得られたPeer IDを期待値と照合する。
5. handshake completeとconfirmedを別状態にする。初期実装は保守的に、
   相手認証とhandshake confirmedの両方を満たしてからアプリケーションを開放する。
   ACK・CRYPTO・HANDSHAKE_DONEなど必要な制御処理はそれ以前も進める。
6. 双方向ストリームを開き、長さ付きのmultistreamヘッダとPingのIDを交渉する。
7. 32バイトを送信し、同じ32バイトの応答を検証する。反対側が開始するケースも行う。
8. ストリームのhalf-close、接続close、draining、資源回収まで扱う。

相手認証とアドレス検証は別物である。
Initialの復号成功、Retryの整合性検査、接続元アドレスだけでPeer IDを認証しない。
1パケット=1TLSメッセージ、1ストリームread=1交渉メッセージとは仮定しない。

### 6.2 最低限の仕様台帳

実装時には次の各行をRFC節・テスト・定理へ結び付ける。
接続が一度成功したことを、QUIC全体の完成判定にしない。

| 領域 | 含める義務・境界 |
| --- | --- |
| パケット | coalescing、長さ・CID・varint検査、header protection、packet number復元、AEAD検証 |
| 初期接続 | Version Negotiationの検証、Retry受信とintegrity tag、CIDを結ぶtransport parameterの検証 |
| アドレス | 検証前の最大3倍増幅制限、PATH_CHALLENGE/RESPONSE、NAT rebinding |
| packet number | Initial/Handshake/Applicationの空間分離、重複抑止、nonce非再利用、上限での停止 |
| ACK・損失 | 未送信packetのACK拒否、ACK範囲、RTT、delayed ACK、PTO、損失判定、輻輳・pacing |
| 再送 | 必要なCRYPTO/STREAMデータ等を新しいpacket numberへ再パケット化。暗号文の単純再送ではない |
| フロー制御 | 接続・ストリーム単位の送受信上限、MAX_DATA/MAX_STREAM_DATA/MAX_STREAMS、backpressure |
| ストリーム | IDと方向、offsetのoverflow、再構成、final size、FIN/RESET_STREAM/STOP_SENDING |
| CID・終了 | NEW/RETIRE_CONNECTION_ID、受信stateless resetの検証、idle/closing/draining、鍵・状態の破棄 |
| TLS統合 | transport parameter認証、HelloRetryRequest、暗号化レベル制約、鍵の破棄とkey phase更新 |
| 拡張性 | 未知transport parameterの無視と、不正／未知フレーム等の仕様上のエラーを区別する |

受信済みpacket numberを空間ごとに記録し、認証済みの重複については
必要なACKなどを除きTLS／ストリームの意味効果を二重適用しない。
並べ替えられた未受信番号を単純な単調増加チェックで排除しない。
有限の追跡領域から退役した古い範囲はdropする方針を明示し、
未認証の偽装番号で受信済み集合や退役境界を前進させない。

active migrationを行わず抑止を広告しても、NAT rebindingへの処理義務は消えない。
片方向ストリームの受信枠は初期プロファイルでは0とし、方向・上限違反を検査する。
0-RTTを受理／送信しないが、Application packet-number空間と別物として誤実装しない。
セッション再開を提供せず、post-handshakeメッセージの許可／禁止もRFC 9001に従う。

認証失敗パケットは仕様どおり破棄し、未認証データから安易に接続closeを発生させない。
ローカルの容量制限を、RFCが定めた上限として文書化しない。
各MUST/SHOULD/MAYの充足・制約・除外理由を台帳に残す。

不正入力を正常値へ補正したり、検査を飛ばして処理を続けたりしない。
認証前の不正UDPパケットはdrop、認証済みのプロトコル違反は規定のエラー、
未完のストリーム入力は容量・期限内の待機として区別する。
パース失敗後にアプリケーションへ部分結果を配送せず、エラー／計数以外の
状態更新はその遷移の契約で許可したものに限定する。
仕様が許す未知フィールドの無視を、検証失敗の無視と混同しない。

## 7. TLS・Peer ID・暗号

### 7.1 認証の判定

libp2p TLSの認証では、次を独立に検証する。

- TLS 1.3、ALPN、transcript、CertificateVerify、Finishedの整合性。
- クライアントを含む相互認証。証明書は1枚で、自己署名と有効期間が妥当なこと。
- 必須のlibp2p公開鍵拡張 `1.3.6.1.4.1.53594.1.1` が存在すること。
- host keyによる `libp2p-tls-handshake:` と証明書のSubjectPublicKeyInfoの
  連結に対する署名が正しいこと。
- 公開鍵の規定のprotobuf表現からPeer IDを導出すること。
  接続開始側では期待するPeer IDと一致すること。
- 不明なcritical拡張は拒否、不明なnon-critical拡張は無視すること。

単一の自己署名証明書はlibp2pの仕様であり、それ自体は認証の欠陥ではない。
CAチェーン検証・CRL/OCSPによるWeb PKI認証やホスト名照合に置き換えない。
ただし自己署名、時刻、host keyの署名、TLS transcriptの検証は全て必要で、
パースできた証明書を無条件に受け入れてはならない。
host identity keyと証明書署名鍵、鍵交換用鍵は役割を分ける。
libp2p TLSのプロファイルに従い、初期版のクライアントはSNIを送信しない。
DER/protobufの長さ、重複フィールド、署名・公開鍵形式、正規化規則も検証対象とする。

### 7.2 暗号スイートと実装順序

まずAES-128-GCM/SHA-256系を通してQUICのInitialと1-RTTを接続する。
必要なのはAEADだけでなく、AESのheader protection、SHA-256、
HMAC/HKDF、TLS transcript／鍵スケジュール、署名検証・生成である。
Ed25519の実装にはSHA-512も必要になる。

一般的なTLS 1.3準拠を主張する前にはRFC 8446 §9の必須要件を満たす。
別のアプリケーションプロファイルが定めない場合の§9.1の区別は次のとおり。

| 強さ | アルゴリズム |
| --- | --- |
| MUST | TLS_AES_128_GCM_SHA256、secp256r1（P-256）鍵交換 |
| MUST | rsa_pkcs1_sha256（証明書）、rsa_pss_rsae_sha256（CertificateVerify／証明書）、ecdsa_secp256r1_sha256 |
| SHOULD | TLS_AES_256_GCM_SHA384、TLS_CHACHA20_POLY1305_SHA256、X25519鍵交換 |

secp384r1やECDSA/SHA-384を§9.1の必須項目として追加解釈しない。
X25519は相互運用の優先対象とし、推奨スイートの追加・未対応理由も台帳に記録する。
限定したアルゴリズムだけが動く途中段階は「限定テストプロファイル」と表示する。
この表は要件の整理であり、現時点の準拠宣言ではない。

libp2pの必須host keyであるEd25519を実装し、Ethereum向けの
secp256k1 identityも初期相互運用対象とする。
TLSのECDSA P-256とhost keyのsecp256k1を同一視しない。
RSA/ECDSA host keyなどの追加対応は、TLSの必須署名方式とは別に台帳で管理する。

既存の[EverQuic][everquic]や[HACL*/EverCrypt][hacl]は、
仕様・アルゴリズム・検証手法・テストの再利用候補である。
EverQuicの参照実装はQUICのheader/packet protectionを扱うF*/Low*からCへの実装で、
その証明はLean/RV64の証明でもQUIC全体の証明でもない。
ライセンスとRFC版の差を調べ、採用箇所の対応を証明し直す。

開発用の比較対象に外部暗号／TLS実装を使っても、最終ランタイムの
隠れた代替経路にはしない。外部実装を仮定した段階の証明は条件付きと表示する。
最初の完成した相互運用マイルストーンには、選択した経路の暗号処理もASMを使う。

M2は次の依存順で小さく進め、各群について同じ終了条件を適用する。

| 群 | 対象 |
| --- | --- |
| M2a | SHA-256/SHA-512、HMAC/HKDF、鍵・署名のバイト形式 |
| M2b | AES、GCM、header protection、QUICの鍵／nonce導出 |
| M2c | 有限体演算、鍵交換、署名生成／検証、証明書・Peer ID認証 |

各プリミティブは、独立したLean仕様と公開ベクトルを先に用意し、SAsm実装の
入出力・失敗結果・メモリ・命令数をその仕様へ結ぶ定理を成立させる。
生成命令列を実行して仕様と照合し、C/F*の既存実装との比較は独立したテスト証拠にする。
外部参照実装との一致テストだけで、ASM対応定理や定数時間性の代用にはしない。

参照実装を呼ぶハーネスはtest専用ターゲットへ隔離する。
開発用アダプタがある場合もM2の各群を完了する時点で対象ランタイムから除外し、
M3の統合核には成立したASMプリミティブだけを接続する。
M5ではimport・リンク依存・生成物の呼び出し先を監査して、外部暗号／TLSや
Lean仕様を通常コンパイルした別実装へ迂回していないことも確認する。

### 7.3 セキュリティ上の別証明

機能的正しさだけでは秘密保持・認証の暗号学的安全性を証明したことにならない。
秘密依存の分岐・メモリアドレスを避ける定数時間性は別の観測モデルで検証する。
命令の実機タイミング、キャッシュ、投機、OSなどの仮定は別途明記する。
乱数の品質、暗号学的困難性、実機サイドチャネルをLeanの計算正しさだけから導かない。

秘密鍵・traffic secret・平文を通常ログへ出さない。
鍵の寿命、失敗時の破棄、メモリ消去、再利用禁止を契約に含める。
本番で固定鍵や決定的テスト乱数を利用しない。

## 8. multistream-selectとPing

QUIC varintとmultiformats unsigned varintは別形式として実装する。
multistreamメッセージはUTF-8の文字列と末尾の改行を、
改行込みのバイト長のunsigned varintで前置する。

両側が最初のヘッダを同時送信する場合、複数メッセージが同じreadに入る場合、
1メッセージが多数のreadに分かれる場合を扱う。
未対応のprotocol IDには `na\n`、対応IDには同じIDと末尾改行を返す。
要求・成功応答・拒否応答の全てで、改行込みの長さを前置する同じframingを使う。
選択完了時に余ったバイトをPingへ渡し、読み捨てない。
交渉長・提案回数・時間を制限し、末尾改行欠落や不正長を処理する。
初回はprotocol listingに依存せず、未対応機能を広告しない。

Pingは厳密に32バイトを集約して応答し、同じストリームでの繰り返しにも対応する。
送信側はピアごとに同時に1本を超えるoutbound Pingストリームを保持しない。
受信側は仕様の推奨に合わせて最大2本を受け入れる方針とする。
FIN到達時の不完全な32バイト、half-close、タイムアウト、キャンセルを検査する。
QUIC PING、libp2p Ping、Ethereum Req/Resp Pingを混同しない。

## 9. 証明・テスト・信頼境界

### 9.1 証明の分解

| 段階 | 必要な主張 |
| --- | --- |
| Codec | 正常値の往復、消費長、切り詰め／不正入力の結果、境界外アクセスなし |
| ASM関数 | 全入力の正常／異常結果、メモリ所有権、保存レジスタ、実行命令数上限 |
| 状態遷移 | 状態不変条件の保存、認証前の配送禁止、容量上限、単調な番号・offset |
| Spec対応 | 同じ入力Eventに対するASMの状態・Action・エラーがSpecに対応する |
| トレース | 環境契約下で、反復したイベント処理でも対応が保存される |
| 生成物 | 証明対象の命令列と、配置・relocation後の実行バイナリの対応 |
| ISA | 利用する命令の意味論と標準RISC-Vの対応。Linux全体の検証とは区別する |
| セキュリティ | 定数時間性、暗号仮定、環境仮定、未証明の安全性主張を個別管理する |

実行上限は各関数のlowering後の本体と契約から導く `B_f(Limits, inputLength)`、
使用メモリ上限は領域所有権から導く `M_f(Limits)` として台帳に公開する。
イベントの上限は呼び出し回数の上限と各 `B_f`、dispatcherの命令数から合成する。
`Limits`のquantum予算を超える場合は継続に分割し、その分割自体を検証する。
数値・式・根拠となる定理が揃わない関数は、上限検証済みとしない。

事前条件は実行前に利用できる事実だけにする。
「デコード成功」「相手は正当」といった結果を仮定せず、
成功・エラー・drop・継続を事後条件で表す。
ホストABIのメモリ有効性と、パケット内容の正当性も混同しない。

表現関係と初期状態について到達可能な具体例を持ち、
矛盾した事前条件からの空虚な証明を避ける。
完成した定理はLeanカーネルで検査し、`sorry`や新たな未証明axiomで穴を埋めない。
依存を含む公理集合を監査し、Sail抽出器などの信頼も明記する。

エンコーダ／アセンブラ／リンカを、根拠なく信頼境界から除外しない。
初期は生成物との照合を検証証拠として扱い、
対応定理や検証済みチェッカが成立するまでは、そのツールを信頼境界に残す。
disassembly比較やQEMU成功だけをバイナリの形式証明と呼ばない。

### 9.2 受け入れ試験

1. **仕様ベクトル**: RFC 9001 Appendix A、TLS/暗号の公開ベクトル、
   libp2p TLS証明書、Peer ID、multistream、Pingのバイト列を独立に確認する。
   RFC 8448のTLS例をQUICパケット例としてそのまま使わない。
2. **境界・生成テスト**: varintの幅境界、非最小表現の形式別規則、全ての切断位置、
   overflow、巨大宣言長、不正DER/protobuf、ACK範囲、final sizeを試す。
3. **差分実行**: 同じイベント列をSpecとASM意味論へ与えて比較する。
   続いて同じ生成物をQEMU／実機で動かし、ABI・配置・メモリ表現を照合する。
4. **障害注入**: 損失、重複、並べ替え、MTU、would-block、乱数失敗、
   タイマー失効、鍵更新、NAT rebinding、認証失敗を固定seedで再現する。
5. **相互運用**: go-libp2pとrust-libp2pを独立した対向実装として用いる。
   実行前に版・設定・identity key種別を固定し、通常の暗号・認証を無効化しない。
   双方のdial/listen、双方向ストリーム、Ping反復と正常終了を試す。
6. **負荷・安全性**: 複数接続、同時ストリーム、遅い受信側、容量枯渇を試す。
   §9.1の台帳から当該`Limits`と入力長に対する上限を評価する。
   呼び出し先を含むASM核の入口から出口までの命令数と所有メモリの最大量を測り、
   それぞれが導出上限以下の場合に合格とする。ホスト／OSの命令は混ぜない。
   上限の未登録や超過は不合格であり、実測値に合わせて根拠なく上限を引き上げない。

相互運用は公開mainnetではなく、隔離されたローカルネットワークから始める。
未検証コードを外部へ公開しない。
将来のテスト基準は実行可能コードの80%以上のカバレッジを最低目標とし、
必須仕様と異常分岐の台帳を併用する。カバレッジを証明の代用にはしない。
本書作成時点では、これらの試験を実行したという主張はない。

### 9.3 残る信頼

Leanカーネル、採用したISA仕様／抽出の仮定、
未検証の生成物ツール、ホストABI、OS、ハードウェア、
乱数・時計・鍵保管を明示する。
ネットワークは信頼せず、イベント列は損失・攻撃を含めてモデル化する。
ネットワーク公平性を必要とする進行性は、安全性とは別の条件付き主張にする。

## 10. 実装の順序と終了条件

| 段階 | 成果物と終了条件 |
| --- | --- |
| M0: 基盤の移植可能性 | 依存閉包とライセンス台帳、Linux向けメモリ／ABI、命令部分集合を確定。小さなASM関数の証明と生成物のQEMU実行を接続する |
| M1: バイトと表現 | QUIC varint・unsigned varint・領域アクセスをSpec/ASMで実装。全幅・境界・不正入力と消費長を検証する |
| M2: 暗号と認証部品 | AEAD、header protection、hash/HKDF、鍵交換・署名、DER/protobuf、Peer IDを仕様ベクトルと対応定理で確認する |
| M3: QUIC/TLS接続核 | Initialからhandshake confirmedまで両方向で動作。ACK、損失回復、輻輳、増幅制限、タイマーを障害注入下で確認する |
| M4: ストリームとPing | フロー制御、再構成、multistream-select、Ping、終了・資源回収を同じASM核で接続する |
| M5: 初期相互運用完了 | Linux/RV64上の生成物が既存2実装と通信。認証・暗号を含む対象経路に外部代替実装を使わず、仕様台帳・証明の状態・生成物対応を公開可能な形で記録する |

M0が失敗した場合は、既存モデルの条件を隠して進めず、
独立したメモリモデルと証明基盤の移植範囲を再検討する。
最初から全SAsm拡張を移植しない。実際に使う命令・構造だけを増やす。

暗号・TLS・QUICは相互依存するため、各段階の小さな結合試験は並行して用意する。
ただし、シミュレーションだけ、認証なし、外部QUIC/TLSへの委譲だけで
M5を完了扱いにしない。機能実装、仕様対応証明、定数時間性、
生成物対応の進捗は別列で記録し、未達項目を「検証済み」に含めない。

M5後の候補はEthereum Req/Resp、Gossipsub、discv5、
完全なEthereum P2Pプロファイルに必要なTCP経路である。
その順序と追加スコープは、初期相互運用の結果を受けて別途決める。

## 11. 参照仕様と再現性

規範となるRFC:

- [RFC 9000: QUIC transport](https://www.rfc-editor.org/rfc/rfc9000)
- [RFC 9001: QUIC TLS integration](https://www.rfc-editor.org/rfc/rfc9001)
- [RFC 9002: loss detection and congestion control](https://www.rfc-editor.org/rfc/rfc9002)
- [RFC 8446: TLS 1.3](https://www.rfc-editor.org/rfc/rfc8446)
- [RFC 8448: TLS 1.3 handshake traces](https://www.rfc-editor.org/rfc/rfc8448)

実装着手時に適用するerrataと更新RFCを確認し、仕様台帳へ差分を記録する。

本設計で参照したGit管理仕様は、移動するブランチ名ではなく以下に固定する。

| 参照元 | リビジョン | 対象 |
| --- | --- | --- |
| libp2p/specs | `c750236de43cd8b246a824b377dfdb26bae686db` | [QUIC][libp2p-quic]、[TLS][libp2p-tls]、[接続][libp2p-connections]、[Peer IDs][libp2p-peer-ids]、[Ping][libp2p-ping] |
| multiformats/multistream-select | `9a1fbe8edadebea223f47102f1913b8026c23a1c` | [プロトコル選択][multistream] |
| ethereum/consensus-specs | `204fb4a19774eabb7a2e91505365deed6b8afef8` | [コンセンサス層P2Pプロファイル][ethereum-p2p] |

依存の採用時にはツールチェーン、元コード、テストベクトル、
対向実装のバージョンも固定する。参照しただけのコードやF*側の証明を、
このプロジェクトの実装・証明数へ加算しない。

## 12. 初期設計レビューの判断記録

3回のレビューで得た指摘を以下のとおり処理した。
一部のレビューモデルはエラー／応答なしであり、全員の承認を得たという意味ではない。

| 指摘 | 判断と根拠 |
| --- | --- |
| 受信flood、待機送信、外部要求の上限 | §5.2・§5.4に有限予算、backpressure、完了枠、独立期限を明記した |
| 時計の許容差と停止対象 | §5.1に有限の許容差を追加。壁時計異常は処理中／新規認証、単調時計異常は全接続を対象とする |
| 境界検査の減算underflow | §5.3でlength検査に成功した分岐に限り減算する順序を明記した |
| 送信トークン枯渇時の無期限停止 | §5.2で接続失敗・スロット退役・即時エラーを明記した |
| 未対応protocol IDへの動作 | §2・§8で長さ付きの拒否応答を明記した |
| M0未定義、別節の重複検査が見えない | M0は§10、重複検査は§6.2に定義済み。分割レビューの範囲を文書全体の欠落とは扱わない |
| 悪意あるホストへの耐性がない | 合意した環境契約・信頼境界であり、ホスト侵害への耐性は主張しない。乱数・時刻の正しさを入力形式検査だけで証明しない |
| 切り詰めUDPも有用部分を受理すべき | 不採用。欠けたデータを信用せず全体をdropし、既存ハンドシェイク状態をリセットしない。ネットワーク損失下の回復はQUICが担う |
| TLSの追加アルゴリズムも全てMUST | 不採用。[RFC 8446 §9.1][tls-compliance]はAES-256-GCM、ChaCha20-Poly1305、X25519をSHOULDとし、P-384をMUSTにはしていない |

設計合意時には`Limits`の具体値、移植範囲、ABIの配置、証明・相互運用の実績は未確定だった。
これらはM0以降の成果物として実装台帳へ記録する。本設計だけで実装準備や準拠が完了したとはしない。

[tls-compliance]: https://www.rfc-editor.org/rfc/rfc8446.html#section-9.1
[sasm-ast]: https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/EvmAsm/Rv64/SAsm/Ast.lean
[sasm-flatten]: https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/EvmAsm/Rv64/SAsm/Flatten.lean
[sasm-fn]: https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/EvmAsm/Rv64/SAsm/Fn.lean
[sasm-design]: https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/docs/sasm-design.md
[evm-basic]: https://github.com/Verified-zkEVM/evm-asm/blob/7e65e4d024718f704226cd795f3d03d4e9aafe13/EvmAsm/Rv64/Basic.lean
[riscv-word]: https://github.com/Verified-zkEVM/riscv-zkvm/blob/afcbc45e1c74c2d296e032b5606dd977a304e8ad/RiscvZkvm/Rv64/Word.lean
[riscv-validation]: https://github.com/Verified-zkEVM/riscv-zkvm/blob/afcbc45e1c74c2d296e032b5606dd977a304e8ad/docs/validation.md
[libp2p-quic]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/quic/README.md
[libp2p-tls]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/tls/tls.md
[libp2p-connections]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/connections/README.md
[libp2p-peer-ids]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/peer-ids/peer-ids.md
[libp2p-ping]: https://github.com/libp2p/specs/blob/c750236de43cd8b246a824b377dfdb26bae686db/ping/ping.md
[multistream]: https://github.com/multiformats/multistream-select/blob/9a1fbe8edadebea223f47102f1913b8026c23a1c/README.md
[ethereum-p2p]: https://github.com/ethereum/consensus-specs/blob/204fb4a19774eabb7a2e91505365deed6b8afef8/specs/phase0/p2p-interface.md
[everquic]: https://github.com/project-everest/everquic-crypto
[hacl]: https://github.com/hacl-star/hacl-star
