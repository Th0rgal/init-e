import InitECandidate.Runtime.CeilLog2LoopReturned
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanWhileNoReturn
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.NormalWhileLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem ceilLog2_loop_no_return {F : Type} (state : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) :
    (evaluateHOLFiniteState state (.while ceilLog2Condition ceilLog2Increment)).1 ≠ some (.returned value) := by
  apply evaluate_while_no_return
  intro current result
  exact evaluate_noDirectReturn ceilLog2Increment (by rfl) current result

theorem ceilLog2_return_exposes_loop {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state
      (.seq (.while ceilLog2Condition ceilLog2Increment) (.return (.var .local (ofString "d")))) =
      (some (.returned value),post)) :
    ∃ loopPost, evaluateHOLFiniteState state (.while ceilLog2Condition ceilLog2Increment) = (none,loopPost) ∧
      loopPost.locals.lookup (ofString "d") = some value := by
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases loopRun : evaluateHOLFiniteState state (.while ceilLog2Condition ceilLog2Increment) with
  | mk result loopPost =>
    rw [loopRun] at run
    cases result with
    | some result =>
      have impossible := ceilLog2_loop_no_return state value
      rw [loopRun] at impossible
      exact False.elim (impossible (Prod.mk.inj run).1)
    | none =>
      dsimp only at run
      rw [evaluateHOLFiniteState_return] at run
      cases binding : loopPost.locals.lookup (ofString "d") with
      | none => simp [evalHOLExact,binding] at run
      | some actual =>
        simp only [evalHOLExact,binding] at run
        split at run
        · have equal := PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj run).1)
          exact ⟨loopPost,rfl,by rw [binding,equal]⟩
        · cases run

/-- Every returned value from the original helper is a legal shift amount.
The returned loop guard exposes the input's upper power-of-two bound. -/
theorem ceilLog2_body_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (n : BitVec 64) (value : ValueHOL 64)
    (input : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ceil_log2) =
      (some (.returned value),post)) :
    ∃ d : BitVec 64, d.toNat < 64 ∧ value = .val (.word d) ∧
      n.toNat ≤ ((1#64) <<< d.toNat).toNat := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (.dec (ofString "d") .one (.const (0#64))
    (.seq (.while ceilLog2Condition ceilLog2Increment) (.return (.var .local (ofString "d"))))) = _ at run
  obtain ⟨middle,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "d") (.const (0#64))
    0 _ (some (.returned value)) rfl run
  let entered := setVarHOLFinite (ofString "d") (.val (.word (0#64))) state
  obtain ⟨loopPost,loopRun,binding⟩ := ceilLog2_return_exposes_loop entered middle value bodyRun
  obtain ⟨d,small,counter,guard⟩ := ceilLog2_loop_returned entered loopPost 0
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) (by decide) loopRun
  have valueEq : value = .val (.word d) := by
    rw [counter] at binding
    exact (Option.some.inj binding).symm
  have frame := evaluate_normal_while_local_frame (ofString "n") ceilLog2Condition ceilLog2Increment
    (by rfl) (by rfl) entered loopPost loopRun
  have finalInput : loopPost.locals.lookup (ofString "n") = some (.val (.word n)) := by
    rw [frame]
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "d" ≠ ofString "n" by decide] using input
  refine ⟨d,small,valueEq,?_⟩
  by_contra notBounded
  have less : ((1#64) <<< d.toNat) < n := BitVec.lt_def.mpr (by omega)
  have legal : ¬ (d.toNat ≠ 0 ∧ 64 ≤ d.toNat) := by omega
  simp [ceilLog2Condition,evalHOLFinite_eq_toExact,evalHOLExact,counter,finalInput,
    wordShiftHOL,legal,Compiler.Encoders.Asm.wordCmpHOL,less] at guard

#print axioms ceilLog2_loop_no_return
#print axioms ceilLog2_return_exposes_loop
#print axioms ceilLog2_body_returned
end InitECandidate.Runtime
