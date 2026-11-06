// Test-only authenticated QUIC-v1 peer; never linked into the ASM runtime.
mod options;

use futures::StreamExt;
use libp2p::{PeerId, Swarm, SwarmBuilder, identity, ping, swarm::SwarmEvent};
use serde_json::json;
use std::{collections::HashMap, io::Write, time::Duration};

fn emit(value: serde_json::Value) -> Result<(), std::io::Error> {
    let mut output = std::io::stdout().lock();
    serde_json::to_writer(&mut output, &value)?;
    writeln!(output)
}

fn build(config: &options::Options) -> Result<Swarm<ping::Behaviour>, Box<dyn std::error::Error>> {
    let key = if config.identity == "ed25519" {
        identity::Keypair::generate_ed25519()
    } else {
        identity::Keypair::generate_secp256k1()
    };
    let mut swarm = SwarmBuilder::with_existing_identity(key)
        .with_tokio()
        .with_quic()
        .with_behaviour(|_| {
            ping::Behaviour::new(
                ping::Config::new()
                    .with_interval(Duration::from_millis(300))
                    .with_timeout(Duration::from_secs(10)),
            )
        })?
        .with_swarm_config(|c| c.with_idle_connection_timeout(Duration::from_secs(60)))
        .build();
    swarm.listen_on(config.listen.clone())?;
    Ok(swarm)
}

fn observe(
    event: SwarmEvent<ping::Event>,
    local: PeerId,
    counts: &mut HashMap<PeerId, u32>,
    requested: u32,
) -> Result<(), Box<dyn std::error::Error>> {
    match event {
        SwarmEvent::NewListenAddr { address, .. } => emit(json!({"event": "ready",
            "peer": local.to_string(), "address": address.with_p2p(local).map_err(|_| "peer address")?.to_string(),
            "implementation": "rust-libp2p", "version": "0.57.1"}))?,
        SwarmEvent::ConnectionEstablished { peer_id, .. } => {
            emit(json!({"event": "connected", "peer": peer_id.to_string()}))?
        }
        SwarmEvent::Behaviour(ping::Event { peer, result, .. }) => match result {
            Ok(_) => {
                let round = counts.entry(peer).or_default();
                if *round < requested {
                    *round += 1;
                    emit(json!({"event": "ping", "peer": peer.to_string(), "round": *round}))?;
                    if *round == requested {
                        emit(
                            json!({"event": "done", "peer": peer.to_string(), "count": requested}),
                        )?;
                    }
                }
            }
            Err(_) => {
                emit(json!({"event": "error", "reason": "ping failed", "peer": peer.to_string()}))?
            }
        },
        SwarmEvent::OutgoingConnectionError { .. } => {
            emit(json!({"event": "error", "reason": "authenticated QUIC dial failed"}))?
        }
        _ => {}
    }
    Ok(())
}

async fn run(config: options::Options) -> Result<(), Box<dyn std::error::Error>> {
    let mut swarm = build(&config)?;
    if let Some(address) = config.target {
        swarm.dial(address)?;
    }
    let deadline = tokio::time::sleep(config.lifetime);
    tokio::pin!(deadline);
    let mut term = tokio::signal::unix::signal(tokio::signal::unix::SignalKind::terminate())?;
    let mut counts = HashMap::new();
    loop {
        tokio::select! {
            _ = &mut deadline => break,
            _ = tokio::signal::ctrl_c() => break,
            _ = term.recv() => break,
            event = swarm.select_next_some() => observe(event, *swarm.local_peer_id(), &mut counts, config.count)?,
        }
    }
    let peers: Vec<_> = swarm.connected_peers().copied().collect();
    for peer in peers {
        let _ = swarm.disconnect_peer_id(peer);
    }
    // Drive graceful connection close before dropping the transport.
    let close = tokio::time::sleep(Duration::from_millis(100));
    tokio::pin!(close);
    loop {
        tokio::select! {
            _ = &mut close => break,
            _ = swarm.select_next_some() => {}
        }
    }
    emit(json!({"event": "closed"}))?;
    Ok(())
}

#[tokio::main]
async fn main() {
    if std::env::args().any(|arg| arg == "--help") {
        println!(
            "Usage: rust-peer [--listen <loopback-quic>] [--target <quic-with-p2p-id>] [--identity ed25519|secp256k1] [--count 1..32] [--lifetime <seconds>s]"
        );
        return;
    }
    let result = match options::parse() {
        Ok(config) => run(config).await,
        Err(_) => {
            eprintln!("Invalid test peer arguments.");
            std::process::exit(2);
        }
    };
    if result.is_err() {
        eprintln!("Test peer execution failed.");
        std::process::exit(1);
    }
}
