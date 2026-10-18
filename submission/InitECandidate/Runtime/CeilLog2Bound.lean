import InitECandidate.Runtime.CappedCountedLoop
import InitECandidate.Runtime.OriginalCeilLog2Code
import InitECandidate.Runtime.AllocationInitializersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def ceilLog2Condition : ExpHOL 64 :=
  .cmp .lower (.shift .lsl (.const 1) (.var .local (ofString "d")))
    (.var .local (ofString "n"))

/-- The actual evaluator rejects a shift by the word width. This also bounds
the helper on inputs whose result would otherwise require a 64-bit shift. -/
theorem ceilLog2_guard_at_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (counter : state.locals.lookup (ofString "d") = some (.val (.word 64))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      ceilLog2Condition = none := by
  simp [ceilLog2Condition,evalHOLFinite_eq_toExact,evalHOLExact,counter,wordShiftHOL]

theorem ceilLog2_body_bounded : ProgBounded (sourceFunctionBody Guest.guestFn_ceil_log2) 64 := by
  rw [sourceFunctionBody_eq_structural]
  change ProgBounded (.dec (ofString "d") .one (.const (0#64))
    (.seq (.while ceilLog2Condition (.assign .local (ofString "d")
      (.op .add [.var .local (ofString "d"),.const 1])))
      (.return (.var .local (ofString "d"))))) 64
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  let entered := setVarHOLFinite (ofString "d") (.val (.word (0#64))) state
  let body : ProgHOL 64 := .assign .local (ofString "d")
    (.op .add [.var .local (ofString "d"),.const 1])
  let loop := ProgHOL.while ceilLog2Condition body
  have counter : entered.locals.lookup (ofString "d") = some (.val (.word (0#64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := cappedCountedWhile_run (ofString "d") ceilLog2Condition 64
    (fun next atWidth => Or.inl (ceilLog2_guard_at_width next atWidth))
    (show CountedBody (ofString "d") 1 body 0 from CountedBody.incr)
    64 entered code 0 counter (by decide) (by decide) budget
  have firstBound : entered.clock ≤ (evaluateHOLFiniteState entered loop).2.clock + 64 ∧
      (evaluateHOLFiniteState entered loop).2.clock ≤ entered.clock ∧
      (evaluateHOLFiniteState entered loop).1 ≠ some .timeOut := by
    simpa using bounded
  have combined := evaluate_sequence_code_bounded entered loop (.return (.var .local (ofString "d")))
    64 0 firstBound
    (fun next nextCode _ => ProgBounded.straight (.return (.var .local (ofString "d"))) (by decide)
      next (nextCode.trans code) (by omega)) (by change 64 + 0 ≤ state.clock; omega)
  simpa [entered,loop,body,setVarHOLFinite] using combined

theorem ceilLog2_funBounded : FunBounded (ofString "ceil_log2") 64 :=
  ⟨_,_,_,originalRuntimeCode_ceilLog2_lookup,ceilLog2_body_bounded⟩

#print axioms ceilLog2_guard_at_width
#print axioms ceilLog2_body_bounded
#print axioms ceilLog2_funBounded
end InitECandidate.Runtime
