# ローカル相互運用の対向ピア

**このディレクトリは独立した対向実装のfixtureです。ASM核の代替実装ではありません。**
現在の `check_peers.py` はGoとRust同士の検査であり、
libp2p-asmとの相互運用が完了したという証拠ではありません。

| 対向実装 | 固定版 | コンパイラ |
| --- | --- | --- |
| go-libp2p | v0.51.0（03349944847387886bf06b65993b2a03c1e6d12d） | Go 1.26.9 |
| rust-libp2p | 0.57.1（crates.io checksumはCargo.lock） | Rust 1.97.1 |

推移依存は `go.sum`／`Cargo.lock` で固定します。
Go 1.21以降の自動toolchain取得とRustupを利用します。
初回は公開依存のダウンロードが必要です。

## ビルドとfixtureの検査

リポジトリのルートから実行します。

```sh
(cd tests/interop/go && go mod download && go test ./... && \
  go build -o ../../../build/interop/go-peer .)
(cd tests/interop/rust && cargo test --locked && cargo build --locked)
cp build/interop/rust-target/debug/libp2p-asm-interop-peer build/interop/rust-peer
python3 tests/interop/check_peers.py
```

出力とイベント記録は `build/interop/` に置きます。
両者のdial/listen、Ed25519／secp256k1の4組、IPv4／IPv6の計16ケースで、
期待したPeer IDとの接続、双方向各3回のPing、正常な停止を検査します。
2026-11-06にこの16ケースを実行し、全て通過しました。

## 単体での起動

```sh
build/interop/go-peer --identity secp256k1 --lifetime 30s
build/interop/rust-peer --identity ed25519 --lifetime 30s
```

`--listen` の既定値は `/ip4/127.0.0.1/udp/0/quic-v1`。
IPv6では `/ip6/::1/udp/0/quic-v1` を指定します。
stdoutのJSON `ready.address` をもう一方の `--target` に渡すとdialします。
targetには期待する `/p2p/<Peer ID>` が必須です。
両側とも接続後にoutbound Pingを開始し、相手のPingにも応答します。

stdoutは `ready`、`connected`、`ping`、`done`、`error`、`closed` のJSON行、
診断はstderrです。`--count` は1〜32、`--lifetime` は1〜60秒。
`done` は要求したoutbound回数の達成であり、プロセスは期限またはSIGTERM/SIGINTまで
受信側として残ります。Rustの標準Ping behaviourはその間も通常のprobeを継続します。

loopback以外、TCP、DNS、relay、余分なmultiaddress要素を拒否します。
QUICのTLS認証・証明書検証・期待Peer ID検証を無効化していません。
identityは各起動時にOS乱数から生成し、秘密鍵を出力・保存しません。
これらの依存はtest-onlyで、Lean/ASMの本番核へリンクしません。
