import InitECandidate.Runtime.RlpHeaderLongStringFullContract
import InitECandidate.Runtime.RlpHeaderLongStringReader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full checked dispatch retains the actual successful length-reader execution. -/
theorem rlpHeader_long_string_full_return_reader {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (nonzero : length ≠ 0) (lower : 183 < byte.toNat) (upper : byte.toNat ≤ 191)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned value),post)) :
    ∃ (payload : BitVec 64) (readerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite
        (setVarHOLFinite (ofString "ll") (.val (.word ((BitVec.ofNat 64 byte.toNat) - 183)))
          (setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state))
        (rlpReadLengthCallee (pointer + 1) ((BitVec.ofNat 64 byte.toNat) - 183)))
        (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned (.val (.word payload))),readerPost) ∧
      value = rlpHeaderLongStringValue ((BitVec.ofNat 64 byte.toNat) - 183) payload ∧
      payload.toNat < length.toNat ∧
      0 < (1 + (((BitVec.ofNat 64 byte.toNat) - 183) + payload)).toNat ∧
      (1 + (((BitVec.ofNat 64 byte.toNat) - 183) + payload)).toNat ≤ length.toNat := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : length ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.var .local (ofString "p"))) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [evalHOLExact,pointerLocal,loaded]
  rw [source_rlpHeader_body,evaluateHOLFiniteState_seq_line780,check] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "b")
    (.loadByte (.var .local (ofString "p"))) (BitVec.ofNat 64 byte.toNat) rlpHeaderAfterByte
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have frame : ∀ name, name ≠ ofString "b" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have low : 183 < (BitVec.ofNat 64 byte.toNat).toNat := by change 183 < byte.toNat % 2^64; omega
  have high : (BitVec.ofNat 64 byte.toNat).toNat ≤ 191 := by change byte.toNat % 2^64 ≤ 191; omega
  rw [evaluate_rlpHeader_long_string_after_load entered pointer (BitVec.ofNat 64 byte.toNat) ((frame _ (by decide)).trans pointerLocal) atByte low high code ticks] at bodyRun
  exact rlpHeader_long_string_return_reader entered output pointer (BitVec.ofNat 64 byte.toNat) length value
    ((frame _ (by decide)).trans pointerLocal) atByte ((frame _ (by decide)).trans lengthLocal)
    low high nonzero code (by change 10 ≤ state.clock; omega) bodyRun


#print axioms rlpHeader_long_string_full_return_reader
end InitECandidate.Runtime
