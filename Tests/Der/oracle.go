// Test-only independent DER parsing through Go's standard ASN.1 implementation.
package main

import (
	"bufio"
	"encoding/asn1"
	"encoding/hex"
	"encoding/json"
	"fmt"
	"os"
)

type result struct {
	OK bool `json:"ok"`
	Fields []int `json:"fields"`
}

func main() {
	scanner := bufio.NewScanner(os.Stdin)
	encoder := json.NewEncoder(os.Stdout)
	for scanner.Scan() {
		data, err := hex.DecodeString(scanner.Text())
		if err != nil {
			panic("invalid test fixture")
		}
		var value asn1.RawValue
		rest, err := asn1.Unmarshal(data, &value)
		r := result{OK: err == nil}
		if r.OK {
			r.Fields = []int{int(data[0]), len(value.FullBytes)-len(value.Bytes),
				len(value.Bytes), len(data)-len(rest)}
		}
		if err := encoder.Encode(r); err != nil {
			panic("oracle output failed")
		}
	}
	if err := scanner.Err(); err != nil {
		fmt.Fprintln(os.Stderr, "oracle input failed")
		os.Exit(1)
	}
}
