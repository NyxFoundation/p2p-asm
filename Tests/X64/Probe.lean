import Tests.X64
import Tests.QuicWire.Probe
import Tests.Streams.Probe

open Libp2pAsm

def main (args : List String) : IO Unit := do
  match args with
  | ["emit-fixtures", directory] => Tests.X64.emitFixtures directory
  | ["quic", kind, directory] => Tests.QuicWire.run kind directory
  | ["streams", kind, directory] => Tests.Streams.main [kind, directory]
  | _ => throw (IO.userError "usage: x64-probe emit-fixtures DIR | (quic|streams) KIND DIR")
