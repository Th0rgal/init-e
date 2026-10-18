import InitECandidate.Runtime.RlpSlicesLoopGlobalsBound
import InitECandidate.Runtime.RlpSlicesLoopReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original final return exposes the same array/count pair and retains
all filled readable entries in the returned state's concrete memory. -/
theorem rlpSlices_loop_return_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer count array : BitVec 64) (valid : RlpSlicesMemoryWitness state pointer count array)
    (budget : (count.toNat - valid.control.index.toNat) * 12 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpSlicesLoopAndReturn = (some (.returned value),post)) :
    value = .rStruct [.val (.word array),.val (.word count)] ∧ RlpSlicePrefix post array count.toNat ∧ post.globals = state.globals := by
  obtain ⟨result,loopPost,loopRun,_,_,_,done,noReturn⟩ := evaluate_rlpSlices_loop_globals_bounded state pointer count array valid budget
  rw [source_rlpSlices_loop_and_return,evaluateHOLFiniteState_seq_line780,loopRun] at run
  cases result with
  | some result => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    obtain ⟨next,_,filled,globals⟩ := done rfl
    have returned : evaluateHOLFiniteState loopPost
        (.return (.rstruct [.var .local (ofString "arr"),.var .local (ofString "count")])) =
        (some (.returned (.rStruct [.val (.word array),.val (.word count)])),emptyLocalsHOLFinite loopPost) := by
      simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,next.arrayLocal,next.control.countLocal,
        shapeOfHOLExact,sizeOfShapeWithContextHOL]
    have equal := Prod.mk.inj (run.symm.trans returned)
    refine ⟨PanSemResultExact.returned.inj (Option.some.inj equal.1),?_⟩
    rw [equal.2]
    refine ⟨?_,globals⟩
    intro slot inside
    obtain ⟨p,n,entry⟩ := filled slot inside
    exact ⟨p,n,RlpSliceEntry.after_frame loopPost _ _ _ _ _ entry rfl rfl rfl⟩

#print axioms rlpSlices_loop_return_globals
end InitECandidate.Runtime
