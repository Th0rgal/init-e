import InitECandidate.Runtime.RlpSlicesLoopReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpSlicesInitialized : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_list_to_slices with
  | .decCall _ _ _ _ (.decCall _ _ _ _ body) => body
  | _ => .skip

theorem source_rlpSlices_initialized : rlpSlicesInitialized =
    .dec (ofString "i") .one (.const 0)
      (.dec (ofString "off") .one (.const 0) rlpSlicesLoopAndReturn) := by
  simp only [rlpSlicesInitialized,rlpSlicesLoopAndReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original zero-initialized index/offset scopes establish the loop
invariant and restore old locals without adding source ticks. -/
theorem evaluate_rlpSlices_initialized_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) (budget : count.toNat * 12 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpSlicesInitialized
    state.clock ≤ evaluated.2.clock + count.toNat * 12 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let initial := setVarHOLFinite (ofString "off") (.val (.word (0 : BitVec 64)))
    (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state)
  have atPointer : initial.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "p" by decide,show ofString "i" ≠ ofString "p" by decide] using pointerLocal
  have atCount : initial.locals.lookup (ofString "count") = some (.val (.word count)) := by
    simpa [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "off" ≠ ofString "count" by decide,show ofString "i" ≠ ofString "count" by decide] using countLocal
  have atOffset : initial.locals.lookup (ofString "off") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atIndex : initial.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [initial,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  let valid : RlpSlicesLoopWitness initial pointer count :=
    ⟨0,0,atPointer,atCount,atOffset,atIndex,by simp,code⟩
  have bound := evaluate_rlpSlices_loop_and_return_bounded initial pointer count valid
    (by change count.toNat * 12 ≤ state.clock; exact budget)
  rw [source_rlpSlices_initialized,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  cases run : evaluateHOLFiniteState initial rlpSlicesLoopAndReturn with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_rlpSlices_initialized_bounded
end InitECandidate.Runtime
