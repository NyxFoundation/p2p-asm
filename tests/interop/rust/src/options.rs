use libp2p::{Multiaddr, multiaddr::Protocol};
use std::time::Duration;

pub struct Options {
    pub listen: Multiaddr,
    pub target: Option<Multiaddr>,
    pub identity: String,
    pub count: u32,
    pub lifetime: Duration,
}

pub fn local_quic(value: &str) -> Result<Multiaddr, String> {
    let address: Multiaddr = value.parse().map_err(|_| "invalid multiaddress")?;
    let mut fields = address.iter();
    let local = match fields.next() {
        Some(Protocol::Ip4(ip)) => ip.is_loopback(),
        Some(Protocol::Ip6(ip)) => ip.is_loopback(),
        _ => false,
    };
    if !local
        || !matches!(fields.next(), Some(Protocol::Udp(_)))
        || !matches!(fields.next(), Some(Protocol::QuicV1))
    {
        return Err("test peers require loopback UDP/QUIC-v1".into());
    }
    if !matches!(fields.next(), None | Some(Protocol::P2p(_))) || fields.next().is_some() {
        return Err("invalid test address structure".into());
    }
    Ok(address)
}

pub fn parse() -> Result<Options, String> {
    let mut result = Options {
        listen: local_quic("/ip4/127.0.0.1/udp/0/quic-v1")?,
        target: None,
        identity: "ed25519".into(),
        count: 3,
        lifetime: Duration::from_secs(30),
    };
    let mut args = std::env::args().skip(1);
    while let Some(name) = args.next() {
        let value = args.next().ok_or("missing option value")?;
        match name.as_str() {
            "--listen" => result.listen = local_quic(&value)?,
            "--target" => {
                let target = local_quic(&value)?;
                if !matches!(target.iter().last(), Some(Protocol::P2p(_))) {
                    return Err("target requires an expected Peer ID".into());
                }
                result.target = Some(target);
            }
            "--identity" if value == "ed25519" || value == "secp256k1" => result.identity = value,
            "--count" => result.count = value.parse().map_err(|_| "invalid count")?,
            "--lifetime" => {
                let seconds = value
                    .strip_suffix('s')
                    .ok_or("lifetime must use whole seconds")?;
                result.lifetime =
                    Duration::from_secs(seconds.parse().map_err(|_| "invalid lifetime")?);
            }
            _ => return Err("unknown or invalid option".into()),
        }
    }
    if !(1..=32).contains(&result.count)
        || result.lifetime.is_zero()
        || result.lifetime > Duration::from_secs(60)
    {
        return Err("invalid test peer limits".into());
    }
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn should_reject_nonlocal_or_non_quic_addresses() {
        for address in [
            "/ip4/0.0.0.0/udp/1/quic-v1",
            "/ip4/192.0.2.1/udp/1/quic-v1",
            "/ip4/127.0.0.1/tcp/1",
            "/dns4/localhost/udp/1/quic-v1",
            "/ip4/127.0.0.1/ip4/192.0.2.1/udp/1/quic-v1",
            "/ip4/127.0.0.1/udp/1/quic-v1/p2p-circuit",
        ] {
            assert!(local_quic(address).is_err());
        }
    }

    #[test]
    fn should_accept_loopback_quic_addresses() {
        assert!(local_quic("/ip4/127.0.0.1/udp/0/quic-v1").is_ok());
        assert!(local_quic("/ip6/::1/udp/0/quic-v1").is_ok());
    }
}
