import InitECandidate.Runtime.RlpUncheckedLongReader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned unchecked function exposes the actual after-byte execution. -/
theorem rlpUnchecked_returned_after_load {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) =
      (some (.returned value),post)) :
    ∃ output, evaluateHOLFiniteState
      (setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state)
      rlpUncheckedAfterByte = (some (.returned value),output) := by
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.loadByte (.var .local (ofString "p"))) = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [evalHOLExact,pointerLocal,loaded]
  rw [source_rlpUnchecked_body] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "b")
    (.loadByte (.var .local (ofString "p"))) (BitVec.ofNat 64 byte.toNat) rlpUncheckedAfterByte
    (some (.returned value)) initializer run
  exact ⟨output,bodyRun⟩

#print axioms rlpUnchecked_returned_after_load
end InitECandidate.Runtime
