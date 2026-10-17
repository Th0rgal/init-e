import InitECandidate.Runtime.RlpUncheckedDispatchFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original unchecked length helper preserves memory and globals
with a ten-tick budget, including inaccessible bytes and malformed long lengths. -/
theorem evaluate_rlpUnchecked_body_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked)
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer with
  | none =>
    rw [source_rlpUnchecked_body,evaluateHOLFiniteState_dec_total]
    simp [evalHOLExact,pointerLocal,loaded]
  | some byte =>
    let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) state
    have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "b" ≠ ofString "p" by decide] using pointerLocal
    have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have byteBound := byte.toNat_lt_size
    change byte.toNat < 256 at byteBound
    have bound := evaluate_rlpUnchecked_after_load_frame entered pointer (BitVec.ofNat 64 byte.toNat) atPointer atByte
      (by change byte.toNat % 2^64 ≤ 255; omega) code ticks
    rw [source_rlpUnchecked_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,pointerLocal,loaded,Option.map_some,shapeOfHOLExact,shapeEqHOL,if_true]
    cases run : evaluateHOLFiniteState entered rlpUncheckedAfterByte with
    | mk result post =>
      rw [run] at bound
      exact bound

#print axioms evaluate_rlpUnchecked_body_frame
end InitECandidate.Runtime
