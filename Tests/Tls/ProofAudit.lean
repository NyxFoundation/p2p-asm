import Libp2pAsm.Refinement.Tls.Encoding
import Libp2pAsm.Refinement.Tls.Helpers
import Libp2pAsm.Refinement.Tls.Leaf
import Libp2pAsm.Refinement.Tls.Transcript

#print axioms Libp2pAsm.Refinement.Tls.vector_length
#print axioms Libp2pAsm.Refinement.Tls.header16_roundtrip
#print axioms Libp2pAsm.Refinement.Tls.header8_roundtrip
#print axioms Libp2pAsm.Refinement.Tls.encode_workspace_alignment
#print axioms Libp2pAsm.Refinement.Tls.encode_workspace_bound
#print axioms Libp2pAsm.Refinement.Tls.encode_workspace_correspondence
#print axioms Libp2pAsm.Refinement.Tls.decode_budget_word
#print axioms Libp2pAsm.Refinement.Tls.encode_budget_word
#print axioms Libp2pAsm.Refinement.Tls.quic_reject_record
#print axioms Libp2pAsm.Refinement.Tls.quic_reject_key_update
#print axioms Libp2pAsm.Refinement.Tls.header_shift_or_fragment
#print axioms Libp2pAsm.Refinement.Tls.uint24_accumulate_bound
#print axioms Libp2pAsm.Refinement.Tls.header_shift_or_in_reader
#print axioms Libp2pAsm.Refinement.Tls.take_success_bounds
#print axioms Libp2pAsm.Refinement.Tls.take_remaining
#print axioms Libp2pAsm.Refinement.Tls.vector24_bounds
#print axioms Libp2pAsm.Refinement.Tls.header24_roundtrip
#print axioms Libp2pAsm.Refinement.Tls.bitmap_address_bound
#print axioms Libp2pAsm.Refinement.Tls.distinct_bitmap_position
#print axioms Libp2pAsm.Refinement.Tls.span_nonwrap_last
#print axioms Libp2pAsm.Refinement.Tls.staged_regions_separate
#print axioms Libp2pAsm.Refinement.Tls.schedule_label_handshake
#print axioms Libp2pAsm.Refinement.Tls.schedule_label_finished
#print axioms Libp2pAsm.Refinement.Tls.finished_context_empty
#print axioms Libp2pAsm.Refinement.Tls.hrr_synthetic_header
#print axioms Libp2pAsm.Refinement.Tls.remaining_fragment
#print axioms Libp2pAsm.Refinement.Tls.remaining_in_need
#print axioms Libp2pAsm.Refinement.Tls.cursor_subtraction_exact
#print axioms Libp2pAsm.Refinement.Tls.execute_status_and_wipe
#print axioms Libp2pAsm.Refinement.Tls.record_reject_path_in_leaf
#print axioms Libp2pAsm.Refinement.Tls.keyupdate_reject_path_in_leaf
#print axioms Libp2pAsm.Refinement.Tls.wipe_preserves_saved
#print axioms Libp2pAsm.Refinement.Tls.wipe_preserves_memory
#print axioms Libp2pAsm.Refinement.Tls.wipe_status
#print axioms Libp2pAsm.Refinement.Tls.transcript_hash_size
#print axioms Libp2pAsm.Refinement.Tls.synthetic_message_size
