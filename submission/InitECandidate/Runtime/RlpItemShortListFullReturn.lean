import InitECandidate.Runtime.RlpItemShortListDispatchReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful original short-list parsing returns exact fields and
positive input-bounded consumed length through both restored local scopes. -/
theorem rlpItem_short_list_full_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 191 < byte.toNat) (upper : byte.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    value = .rStruct [.val (.word 1),.val (.word (pointer + 1)),.val (.word ((BitVec.ofNat 64 byte.toNat) - 192)),.val (.word (1 + ((BitVec.ofNat 64 byte.toNat) - 192)))] ∧
      ((BitVec.ofNat 64 byte.toNat) - 192).toNat < total.toNat ∧ 0 < (1 + ((BitVec.ofNat 64 byte.toNat) - 192)).toNat ∧
      (1 + ((BitVec.ofNat 64 byte.toNat) - 192)).toNat ≤ total.toNat := by
  have check : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.var .local (ofString "len")) (.const 0))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 1]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite]
    have notZero : total ≠ BitVec.ofNat 64 0 := nonzero
    simp [evalHOLExact,totalLocal,Compiler.Encoders.Asm.wordCmpHOL,notZero,evaluateHOLFiniteState_skip]
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.var .local (ofString "p"))) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [evalHOLExact,pointerLocal,loaded]
  rw [source_rlpItem_body,evaluateHOLFiniteState_seq_line780,check] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "b")
    (.loadByte (.var .local (ofString "p"))) (BitVec.ofNat 64 byte.toNat) rlpItemAfterByte
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
  have frame : ∀ name, name ≠ ofString "b" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    rw [frame _ (by decide)]
    exact totalLocal
  exact rlpItem_short_list_after_load_return_contract entered output pointer (BitVec.ofNat 64 byte.toNat) total value
    ((frame _ (by decide)).trans pointerLocal) atByte atTotal
    (by change 191 < byte.toNat % 2^64; omega) (by change byte.toNat % 2^64 ≤ 247; omega)
    nonzero code ticks bodyRun

#print axioms rlpItem_short_list_full_return_contract
end InitECandidate.Runtime
