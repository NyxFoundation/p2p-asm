// Test-only adapter to quic-go v0.59.0, with extensions disabled.
package main

import (
 "bufio"
 "encoding/hex"
 "encoding/json"
 "os"

 "github.com/quic-go/quic-go/internal/protocol"
 "github.com/quic-go/quic-go/internal/wire"
 "github.com/quic-go/quic-go/quicvarint"
)

type request struct { Kind string; Hex string; Server bool }
type result struct { OK bool; Consumed int; Canonical string; Detail any }

func frame(b []byte) result {
 t,n,e:=quicvarint.Parse(b)
 if e!=nil { return result{} }
 if t==0 { return result{OK:true,Consumed:n,Canonical:"00"} }
 p:=wire.NewFrameParser(false,false,false)
 typ,used,e:=p.ParseType(b,protocol.Encryption1RTT)
 if e!=nil { return result{} }
 var f wire.Frame
 var count int
 switch {
 case t>=8 && t<=15:
  f,count,e=p.ParseStreamFrame(typ,b[used:],protocol.Version1)
 case t==2 || t==3:
  f,count,e=p.ParseAckFrame(typ,b[used:],protocol.Encryption1RTT,protocol.Version1)
 default:
  f,count,e=p.ParseLessCommonFrame(typ,b[used:],protocol.Version1)
 }
 if e!=nil { return result{} }
 encoded,_:=f.Append(nil,protocol.Version1)
 return result{OK:true,Consumed:used+count,Canonical:hex.EncodeToString(encoded),Detail:f}
}

func run(r request) result {
 b,e:=hex.DecodeString(r.Hex)
 if e!=nil { return result{} }
 if r.Kind=="frame" { return frame(b) }
 if r.Kind=="packet" {
  h,part,_,e:=wire.ParsePacket(b)
  return result{OK:e==nil,Consumed:len(part),Detail:h}
 }
 p:=new(wire.TransportParameters)
 who:=protocol.PerspectiveClient
 if r.Server { who=protocol.PerspectiveServer }
 e=p.Unmarshal(b,who)
 return result{OK:e==nil,Consumed:len(b),Detail:p}
}

func main() {
 s:=bufio.NewScanner(os.Stdin)
 s.Buffer(make([]byte,4096),1<<20)
 out:=json.NewEncoder(os.Stdout)
 for s.Scan() {
  var r request
  if e:=json.Unmarshal(s.Bytes(),&r);e!=nil { panic(e) }
  if e:=out.Encode(run(r));e!=nil { panic(e) }
 }
 if e:=s.Err();e!=nil { panic(e) }
}
