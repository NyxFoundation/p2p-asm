---
title: Limitsと時計
last_updated: 2026-11-06
tags:
  - resource-limits
  - clock
  - abi
---

# Limitsと時計

## 有限のローカル方針

唯一の設定元は `Libp2pAsm/Spec/Limits/Types.lean`。
`Limits.validate` は、全61項目が正の64ビット値であることと組間の整合性を検査する。
既定値の妥当性と予約量はLeanカーネルで計算確認している。
これは設定の検査であり、未実装のdispatcher・allocatorが既に制限を強制するという意味ではない。
RFCの上限とローカルの容量を混同しない。

| 組 | 主要な既定値 |
| --- | --- |
| 接続 | 全体16、送信元別4、handshake全体8／送信元別2、送信元記録64 |
| 開始 | 1秒に全体16／送信元別4、handshake期限10秒 |
| UDP | 最大2048バイト、batch 32、1秒に1024データグラム／2 MiB、保留受信64 |
| ストリーム | 接続あたり8、各方向64 KiB、CRYPTO各方向64 KiB |
| 追跡 | ACK範囲64、受信PN 4096、送信履歴128、path 2、active CID 8 |
| キュー | Event 1024、完了予約640、アプリ要求64、保留送信64 |
| 要求 | timer 512、entropy 32、clock 16、continuation 32、quantumのAction 16 |
| 実行 | quantum 2^24命令、接続別2^28／全体2^30命令毎秒 |
| メモリ | arena 32 MiB、接続metadata／crypto scratch各64 KiB、stack 16 KiB |
| 待機 | send 5秒・16試行、entropy／clock各1秒、idle 60秒、交渉／Ping各10秒 |
| libp2p | inbound Ping 2／outbound 1、交渉1024バイト・8提案、証明書16 KiB |

Initialの1200バイトを収容し、IPv4/IPv6共通の非jumbo UDPサイズ範囲を使用する。
これは性能測定に基づく最適値ではなく、有限の開発用方針である。
必須機能と各関数の命令・メモリ上限定理への接続は、統合時の終了条件として残る。

完了予約には `maxTimers + maxPendingSends + maxEntropyRequests + maxClockRequests`
が必要で、既定値は624枠。640枠を確保し、受信・アプリ要求が使用しない。
timer予約は接続のidle・3 PN空間・pacing、handshake、stream、
外部要求の期限を計上する。今後追加するtimer種別も同じ台帳へ接続する。

`reservedBytes` は接続metadata、crypto scratch、CRYPTO/stream buffers、
保留送受信データ、256バイトEvent slot、global metadata、stackを計上する。
既定値は **22,560,768バイト**で32 MiBに収まる。
Event slotの256バイトはABI用の予約であり、最終ABI配置の検証は未完了。
この予約式だけで全関数の実際の最大使用量 `M_f` を証明したとはしない。

## 時計源と誤差

開発ホストのPython `time.get_clock_info` で、Linux
`CLOCK_REALTIME` と `CLOCK_MONOTONIC` の公称分解能がともに1 nsであることを確認した。
分解能はUTCの正確さでも、OSスケジューリング遅延の上限でもない。

サンプルは mono-before → realtime → mono-after の順で取得する。
許容サンプル幅は1 ms、経過量の差の許容値は250 ms。
後者は1 nsの分解能とサンプル間隔の測定誤差に余裕を持たせたローカル方針であり、
実時計の精度保証ではない。長すぎるサンプルを信頼せず、誤差許容を無限にしない。
実際のLinuxアダプタによる取得・失敗通知は未実装。

UTCはsigned 64-bit Unix secondsと0..999,999,999のnanosecondsを分離する。
時刻全体を64-bit nanosecondsへ押し込めない。
経過秒の積は `MUL/MULHU` とcarry/borrowで128-bitのまま保持する。
RTCの巻き戻りは許容差以内でも拒否する。

## 時計判定のleaf ABI

`Asm.checkClock` の引数は
`a0=state, a1=sample, a2=maxDriftNs, a3=maxSampleSpanNs`。
両領域は8-byte aligned、互いとコードから分離し、stateは書き込み可能、
sampleは読み取り可能であることが呼び出し側の前提。

- state 32 bytes: mode、previous mono-after、signed UTC seconds、nanoseconds。
- sample 40 bytes: source status、mono-before、mono-after、signed UTC seconds、nanoseconds。
- 各フィールドはLE64。source statusは0=取得成功、1=壁時計失敗、2以上=単調時計失敗。
- 戻り値a0: 0=trusted、1=wall unavailable、2=monotonic failure、
  3=invalid limits、4=invalid state。a1/a2は0。
- stackを使用せず、ra/sp/gp/tpと全s-registersを保存する。

modeは0=初期、1=信頼中、2=壁時計取得不能、3=停止、4=回復候補。
初回の正常サンプルは環境への信頼を前提にanchorとする。
壁時計失敗後は候補を記録し、続く整合したサンプルで認証を再許可する。
jumpを検出したサンプルも候補にとどまり、その時点では再許可しない。
単調時計異常の停止状態はこのAPIでは解除できない。

要求ID・世代による照合とサンプルの時系列順への整理は呼び出し側が先に行う。
遅延した応答をそのまま投入して巻き戻りと誤判定しない。
認証中の鍵破棄、確立済み接続の維持、単調時計異常時の全接続解放は
今後の接続核との統合で実装する責務であり、このleaf単体の効果ではない。

## 現在の検査

`Tests/Clock.lean` は状態遷移、`Tests/ClockAsm.lean` は実命令との対応を検査する。
`tests/native/clocks.py` は509ケースを独立Python整数演算、Leanモデル、
GNU生成および直接エンコードしたQEMU ELFで照合する。
signed epochの両端、64-bitを超える経過量、borrow、guard、保存レジスタを含む。
256という試験fuelは全入力の命令上限定理ではない。
時計ASMの普遍的対応証明・資源上限定理はまだ成立済みとは扱わない。
