import InitECandidate.Runtime.ActualPayloadHeaderCappedReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Statement 40 of `payload_header`: the actual `block_rlp_length(h, pl)` declaration call.  This is
the statement the watched 419-tick construction stops at; everything after it is the serialization
tail that returns the finished header. -/
theorem source_actual_payload_header_block_rlp :
    actualPayloadHeaderAt 40 = .decCall (ofString "bl") .one (ofString "block_rlp_length")
      [.var .local (ofString "h"), .var .local (ofString "pl")] (actualPayloadHeaderAt 41) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 41: the real block-size guard `if 8388608 < bl { raise BlockErr 7 }`. -/
theorem source_actual_payload_header_block_guard :
    actualPayloadHeaderAt 41 = .seq
      (.ite (.cmp .lower (.const (8388608#64)) (.var .local (ofString "bl")))
        (.raise (ofString "BlockErr") (.const (7#64))) .skip) (actualPayloadHeaderAt 42) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 42: the actual `build_mpt_indexed(pl+32, pl+40, txr)` call on the transaction list. -/
theorem source_actual_payload_header_tx_trie :
    actualPayloadHeaderAt 42 = .seq
      (.call (some (none,none)) (ofString "build_mpt_indexed")
        [.load .one (.op .add [.var .local (ofString "pl"), .const (32#64)]),
         .load .one (.op .add [.var .local (ofString "pl"), .const (40#64)]),
         .var .local (ofString "txr")]) (actualPayloadHeaderAt 43) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 43: `nwd := load [pl + 56]`, the withdrawal count. -/
theorem source_actual_payload_header_withdrawal_count :
    actualPayloadHeaderAt 43 = .dec (ofString "nwd") .one
      (.load .one (.op .add [.var .local (ofString "pl"), .const (56#64)]))
      (actualPayloadHeaderAt 44) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 44: the actual allocation of the withdrawal slice array into the global
`wd_rlp_slices`, sized `nwd * 16 + 16`. -/
theorem source_actual_payload_header_withdrawal_slices :
    actualPayloadHeaderAt 44 = .seq
      (.call (some ((some (.global,ofString "wd_rlp_slices")),none)) (ofString "alloc")
        [.op .add [(.panop .mul [.var .local (ofString "nwd"), .const (16#64)]),
          .const (16#64)]]) (actualPayloadHeaderAt 45) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 45: `i := 0`, the withdrawal loop counter. -/
theorem source_actual_payload_header_loop_counter :
    actualPayloadHeaderAt 45 = .dec (ofString "i") .one (.const (0#64)) (actualPayloadHeaderAt 46) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 46: the withdrawal loop `while i < nwd { e := encode_withdrawal_rlp(...);
wd_rlp_slices[i*16] := e.0; wd_rlp_slices[i*16+8] := e.1; i := i+1 }`.  Only its shape at the top
level is asserted here: it is a `seq` whose first component is the loop. -/
theorem source_actual_payload_header_withdrawal_loop :
    ∃ loop : ProgHOL 64, actualPayloadHeaderAt 46 = .seq loop (actualPayloadHeaderAt 47) := by
  unfold actualPayloadHeaderAt
  exact ⟨_,rfl⟩

/-- Statement 47: the actual `build_mpt_indexed(wd_rlp_slices, nwd, wr)` call on the withdrawals. -/
theorem source_actual_payload_header_withdrawal_trie :
    actualPayloadHeaderAt 47 = .seq
      (.call (some (none,none)) (ofString "build_mpt_indexed")
        [.var .global (ofString "wd_rlp_slices"), .var .local (ofString "nwd"),
         .var .local (ofString "wr")]) (actualPayloadHeaderAt 48) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 48: the actual two-word `encode_execution_requests(load [si + 32])` call. -/
theorem source_actual_payload_header_requests :
    actualPayloadHeaderAt 48 = .decCall (ofString "reqs") (.comb [.one,.one])
      (ofString "encode_execution_requests")
      [.load .one (.op .add [.var .local (ofString "si"), .const (32#64)])]
      (actualPayloadHeaderAt 49) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 49: the actual `compute_requests_hash(reqs.0, reqs.1, rh)` call. -/
theorem source_actual_payload_header_requests_hash :
    actualPayloadHeaderAt 49 = .seq
      (.call (some (none,none)) (ofString "compute_requests_hash")
        [.rfield 0 (.var .local (ofString "reqs")), .rfield 1 (.var .local (ofString "reqs")),
         .var .local (ofString "rh")]) (actualPayloadHeaderAt 50) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 50: the actual `keccak256(load [pl + 64], load [pl + 72], bh)` call filling the
block-hashes field of the header. -/
theorem source_actual_payload_header_block_hashes :
    actualPayloadHeaderAt 50 = .seq
      (.call (some (none,none)) (ofString "keccak256")
        [.load .one (.op .add [.var .local (ofString "pl"), .const (64#64)]),
         .load .one (.op .add [.var .local (ofString "pl"), .const (72#64)]),
         .var .local (ofString "bh")]) (actualPayloadHeaderAt 51) := by
  unfold actualPayloadHeaderAt
  rfl

/-- Statement 51: `return h`, the finished header pointer.  This is the value the real call returns
to `run_attempt`. -/
theorem source_actual_payload_header_return :
    actualPayloadHeaderAt 51 = .return (.var .local (ofString "h")) := by
  unfold actualPayloadHeaderAt
  rfl

#print axioms source_actual_payload_header_block_rlp
#print axioms source_actual_payload_header_block_guard
#print axioms source_actual_payload_header_tx_trie
#print axioms source_actual_payload_header_withdrawal_count
#print axioms source_actual_payload_header_withdrawal_slices
#print axioms source_actual_payload_header_loop_counter
#print axioms source_actual_payload_header_withdrawal_loop
#print axioms source_actual_payload_header_withdrawal_trie
#print axioms source_actual_payload_header_requests
#print axioms source_actual_payload_header_requests_hash
#print axioms source_actual_payload_header_block_hashes
#print axioms source_actual_payload_header_return

/-- **The actual returned header pointer.**  Once the body reaches its final statement with `h` bound
to the header base, the real `return h` hands back exactly that word and leaves the memory alone.  This
is the value the `payload_header` declaration call returns to `run_attempt`, so the caller's header
pointer is the same word the construction had at statement 40. -/
theorem actual_payload_header_return_h {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (hLocal : state.locals.lookup (ofString "h") = some (.val (.word pointer))) :
    evaluateHOLFiniteState state (actualPayloadHeaderAt 51) =
      (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite state) := by
  rw [source_actual_payload_header_return]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL,hLocal]

#print axioms actual_payload_header_return_h

end InitECandidate.Runtime
