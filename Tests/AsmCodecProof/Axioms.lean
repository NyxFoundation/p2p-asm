import Tests.AsmCodecProof.Examples
import Tests.AsmCodecProof.Relocation
import Lean.Util.CollectAxioms
import Lean.Elab.Command

-- Fail the build if any proof in this package acquires a nonstandard dependency.
run_cmd do
  let env ← Lean.getEnv
  let roots := [`Libp2pAsm.Rv64.Logic, `Libp2pAsm.Refinement.AsmCodec,
    `Libp2pAsm.Tests.AsmCodecProof]
  let allowed := [`propext, `Quot.sound, `Classical.choice]
  for (name, info) in env.constants.toList do
    if roots.any (·.isPrefixOf name) && info.isTheorem then
      for dependency in ← Lean.collectAxioms name do
        unless allowed.contains dependency do
          throwError "Unexpected dependency in {name}: {dependency}"

-- Audit the dependency closure of every public theorem in this proof package.

-- Libp2pAsm/Rv64/Logic/Bytes.lean
#print axioms Libp2pAsm.Rv64.Logic.Reads.head
#print axioms Libp2pAsm.Rv64.Logic.Reads.tail
#print axioms Libp2pAsm.Rv64.Logic.heap_reads
#print axioms Libp2pAsm.Rv64.Logic.Reads.take
#print axioms Libp2pAsm.Rv64.Logic.shift_or_byte
#print axioms Libp2pAsm.Rv64.Logic.byte_word_bound

-- Libp2pAsm/Rv64/Logic/Fetch.lean
#print axioms Libp2pAsm.Rv64.Logic.fetch_codeAddress
#print axioms Libp2pAsm.Rv64.Logic.fetch_mem

-- Libp2pAsm/Rv64/Logic/Frame.lean
#print axioms Libp2pAsm.Rv64.Logic.execInstr_register_frame
#print axioms Libp2pAsm.Rv64.Logic.execInstr_memory_frame
#print axioms Libp2pAsm.Rv64.Logic.Trace.register_frame
#print axioms Libp2pAsm.Rv64.Logic.Trace.memory_frame

-- Libp2pAsm/Rv64/Logic/Memory.lean
#print axioms Libp2pAsm.Rv64.Logic.heap_valid_congr
#print axioms Libp2pAsm.Rv64.Logic.heap_load_byte
#print axioms Libp2pAsm.Rv64.Logic.heap_store_byte
#print axioms Libp2pAsm.Rv64.Logic.heap_store_valid
#print axioms Libp2pAsm.Rv64.Logic.ByteFrame.refl
#print axioms Libp2pAsm.Rv64.Logic.ByteFrame.store

-- Libp2pAsm/Rv64/Logic/State.lean
#print axioms Libp2pAsm.Rv64.Logic.getReg_atPC
#print axioms Libp2pAsm.Rv64.Logic.memory_atPC
#print axioms Libp2pAsm.Rv64.Logic.pc_atPC
#print axioms Libp2pAsm.Rv64.Logic.atPC_atPC
#print axioms Libp2pAsm.Rv64.Logic.atPC_self
#print axioms Libp2pAsm.Rv64.Logic.setReg_atPC
#print axioms Libp2pAsm.Rv64.Logic.advance_atPC
#print axioms Libp2pAsm.Rv64.Logic.advance_eq_atPC
#print axioms Libp2pAsm.Rv64.Logic.getReg_withMemory
#print axioms Libp2pAsm.Rv64.Logic.pc_withMemory
#print axioms Libp2pAsm.Rv64.Logic.memory_withMemory
#print axioms Libp2pAsm.Rv64.Logic.withMemory_atPC
#print axioms Libp2pAsm.Rv64.Logic.getReg_setReg
#print axioms Libp2pAsm.Rv64.Logic.PreservesCallee.refl
#print axioms Libp2pAsm.Rv64.Logic.PreservesCallee.trans

-- Libp2pAsm/Rv64/Logic/Symbolic.lean
#print axioms Libp2pAsm.Rv64.Logic.jump_eq_atPC
#print axioms Libp2pAsm.Rv64.Logic.storeReg_eq_atPC

-- Libp2pAsm/Rv64/Logic/Trace.lean
#print axioms Libp2pAsm.Rv64.Logic.Trace.append
#print axioms Libp2pAsm.Rv64.Logic.Trace.runLoop
#print axioms Libp2pAsm.Rv64.Logic.Trace.runUntil
#print axioms Libp2pAsm.Rv64.Logic.Total.runUntil
#print axioms Libp2pAsm.Rv64.Logic.step_of_fetch
#print axioms Libp2pAsm.Rv64.Logic.Trace.single
#print axioms Libp2pAsm.Rv64.Logic.Trace.invariant

-- Libp2pAsm/Rv64/Logic/WriteTrace.lean
#print axioms Libp2pAsm.Rv64.Logic.WriteTrace.trace
#print axioms Libp2pAsm.Rv64.Logic.WriteTrace.append
#print axioms Libp2pAsm.Rv64.Logic.writeTrace_at_pc
#print axioms Libp2pAsm.Rv64.Logic.WriteTrace.prefix_store
#print axioms Libp2pAsm.Rv64.Logic.WritesWithin.empty
#print axioms Libp2pAsm.Rv64.Logic.WriteTrace.empty_no_stores
#print axioms Libp2pAsm.Rv64.Logic.write_address_bounds

-- Libp2pAsm/Rv64/Logic/Writes.lean
#print axioms Libp2pAsm.Rv64.Logic.patchBytes_size
#print axioms Libp2pAsm.Rv64.Logic.patchBytes_frame
#print axioms Libp2pAsm.Rv64.Logic.patchBytes_get
#print axioms Libp2pAsm.Rv64.Logic.heap_store_at

-- Libp2pAsm/Refinement/AsmCodec/EncodeArithmetic.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.word_shift_zero_iff
#print axioms Libp2pAsm.Refinement.AsmCodec.word_shift_nonzero

-- Libp2pAsm/Refinement/AsmCodec/EncodeContract.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.encode_memory_frame
#print axioms Libp2pAsm.Refinement.AsmCodec.encodeOutcome_capacity
#print axioms Libp2pAsm.Refinement.AsmCodec.encodeOutcome_error
#print axioms Libp2pAsm.Refinement.AsmCodec.EncodePost.error_memory
#print axioms Libp2pAsm.Refinement.AsmCodec.EncodePost.bytes

-- Libp2pAsm/Refinement/AsmCodec/Errors.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_encode_overflow_trace
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_encode_overflow_trace
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_empty_trace
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_decode_empty_trace

-- Libp2pAsm/Refinement/AsmCodec/Programs.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quicEncode_lower
#print axioms Libp2pAsm.Refinement.AsmCodec.quicDecode_lower
#print axioms Libp2pAsm.Refinement.AsmCodec.unsignedEncode_lower
#print axioms Libp2pAsm.Refinement.AsmCodec.unsignedDecode_lower

-- Libp2pAsm/Refinement/AsmCodec/QuicArithmetic.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.byte_word_nat
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_tag_word
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_width_bound
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_width_word
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_payload_word
#print axioms Libp2pAsm.Refinement.AsmCodec.append_byte_nat
#print axioms Libp2pAsm.Refinement.AsmCodec.foldBytes_nat
#print axioms Libp2pAsm.Refinement.AsmCodec.foldBytes_ofNat

-- Libp2pAsm/Refinement/AsmCodec/QuicCorrect.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.trace_at_pc
#print axioms Libp2pAsm.Refinement.AsmCodec.word_pred
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_body
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_trace

-- Libp2pAsm/Refinement/AsmCodec/QuicDecode.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_header
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_short
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_enter
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_finish

-- Libp2pAsm/Refinement/AsmCodec/QuicEmit.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_emit_prepare
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_emit_write
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_emit_advance
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_emit_store
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_emit_iteration
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_emit_loop

-- Libp2pAsm/Refinement/AsmCodec/QuicEncodeBlocks.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_encode_short
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_initial_shift
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_encode_enter
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_encode_finish

-- Libp2pAsm/Refinement/AsmCodec/QuicEncodeCorrect.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_encode_trace
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_encode_runUntil

-- Libp2pAsm/Refinement/AsmCodec/QuicEntry.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_decode_runUntil
#print axioms Libp2pAsm.Refinement.AsmCodec.quicExample_valid
#print axioms Libp2pAsm.Refinement.AsmCodec.quicExample_result

-- Libp2pAsm/Refinement/AsmCodec/QuicLoop.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.word_length_nonzero
#print axioms Libp2pAsm.Refinement.AsmCodec.word_succ_decrement
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_tail_iteration
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_tail_loop

-- Libp2pAsm/Refinement/AsmCodec/QuicOutput.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quicOutput_length
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_widthTag_bounds
#print axioms Libp2pAsm.Refinement.AsmCodec.quicByte_zero
#print axioms Libp2pAsm.Refinement.AsmCodec.quicByte_header
#print axioms Libp2pAsm.Refinement.AsmCodec.quicOutput_spec

-- Libp2pAsm/Refinement/AsmCodec/QuicSelect.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.quic_select

-- Libp2pAsm/Refinement/AsmCodec/Safety.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.codecs_destinations
#print axioms Libp2pAsm.Refinement.AsmCodec.codecs_callee_saved
#print axioms Libp2pAsm.Refinement.AsmCodec.codecs_return_address
#print axioms Libp2pAsm.Refinement.AsmCodec.decoders_readonly
#print axioms Libp2pAsm.Refinement.AsmCodec.decoders_memory_frame

-- Libp2pAsm/Refinement/AsmCodec/UnsignedArithmetic.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_payload_word
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_flag_word
#print axioms Libp2pAsm.Refinement.AsmCodec.word_shift_ofNat
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_accumulate
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_accumulate_bound

-- Libp2pAsm/Refinement/AsmCodec/UnsignedBranches.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_empty
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_terminal_first
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_terminal_long
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_overflow
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_continue

-- Libp2pAsm/Refinement/AsmCodec/UnsignedCorrect.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_terminal
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_scan
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_decode_trace

-- Libp2pAsm/Refinement/AsmCodec/UnsignedCount.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.SameInputs.trans
#print axioms Libp2pAsm.Refinement.AsmCodec.shift_word_nat
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_count_step
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_count_stop
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_count_loop

-- Libp2pAsm/Refinement/AsmCodec/UnsignedEmit.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_emit_prepare
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_emit_write
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_emit_advance
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_emit_iteration
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_emit_loop

-- Libp2pAsm/Refinement/AsmCodec/UnsignedEncodeBlocks.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_encode_initialize
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_copy_width
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_select
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_encode_short
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_encode_enter
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_encode_finish

-- Libp2pAsm/Refinement/AsmCodec/UnsignedEncodeCorrect.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_encode_trace
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_encode_runUntil

-- Libp2pAsm/Refinement/AsmCodec/UnsignedEntry.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_decode_runUntil
#print axioms Libp2pAsm.Refinement.AsmCodec.unsignedExample_valid
#print axioms Libp2pAsm.Refinement.AsmCodec.unsignedExample_result

-- Libp2pAsm/Refinement/AsmCodec/UnsignedOutput.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsignedOutput_length
#print axioms Libp2pAsm.Refinement.AsmCodec.unsignedByte_nat
#print axioms Libp2pAsm.Refinement.AsmCodec.unsignedOutput_spec

-- Libp2pAsm/Refinement/AsmCodec/UnsignedRead.lean
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_read
#print axioms Libp2pAsm.Refinement.AsmCodec.unsigned_initialize

-- Tests/AsmCodecProof/Examples.lean
#print axioms Libp2pAsm.Tests.AsmCodecProof.quic_entry_valid
#print axioms Libp2pAsm.Tests.AsmCodecProof.unsigned_entry_valid
#print axioms Libp2pAsm.Tests.AsmCodecProof.quic_encoder_example
#print axioms Libp2pAsm.Tests.AsmCodecProof.unsigned_encoder_example
