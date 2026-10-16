import Flapjack.Pancake.Proofs.PanGlobals.SemanticsInitCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.EvaluateClockSubCall

/-- A successful body which preserves its clock executes at every clock with
identical non-clock fields. This uses the original clock-subtraction theorem. -/
theorem pan_initializer_all_clocks {width : Nat} [NeZero width] {F : Type}
    (s post : PanSemStateFiniteExact width F) (body : ProgHOL width)
    (run : evaluateHOLFiniteState {s with locals := HolFiniteMapExact.empty} body = (none,post))
    (clock : post.clock = s.clock) :
    ∀ fuel, evaluateHOLFiniteState {s with locals := HolFiniteMapExact.empty,clock := fuel} body =
      (none,{post with clock := fuel}) := by
  classical
  let tin : PanSemStateFiniteExact width F := {s with locals := HolFiniteMapExact.empty}
  have subtract : Mc tin body :=
    mc_of_pair tin body (evaluateClockSubHOLFinite body (PanPropsEvalStateFiniteExact.ofPanSemFinite tin))
  have zero : evaluateHOLFiniteState {tin with clock := 0} body = (none,{post with clock := 0}) := by
    have initial : evaluateHOLFiniteState tin body =
        (none,{{post with clock := 0} with clock := ({post with clock := 0}).clock + s.clock}) := by
      rw [show tin = {s with locals := HolFiniteMapExact.empty} from rfl,run]
      congr 1
      simp only [Nat.zero_add]
      rw [← clock]
    have h := subtract none {post with clock := 0} s.clock initial (by simp)
    simpa only [tin,Nat.sub_self] using h
  intro fuel
  have added := panPropsEvaluateAddClockEq body {tin with clock := 0} none
    {post with clock := 0} fuel ⟨zero,by simp⟩
  simpa only [tin,Nat.zero_add] using added

/-- Global lowering's generated entry wrapper costs exactly one additional
source clock; it preserves the actual inner run's result and final FFI. -/
theorem pan_init_call_one_clock {width : Nat} [NeZero width] {F : Type}
    (s initialized : PanSemStateFiniteExact width F) (start next : MlS)
    (body functionBody : ProgHOL width) (params : List (MlS × ShapeHOL)) (shape : ShapeHOL)
    (entry : s.code.lookup start = some ([],.seq body (.call none next []),shape))
    (function : s.code.lookup next = some (params,functionBody,shape))
    (initialRun : evaluateHOLFiniteState {s with locals := HolFiniteMapExact.empty} body = (none,initialized))
    (clock : initialized.clock = s.clock)
    (fuel : Nat) (result : Option (PanSemResultExact width)) (post : PanSemStateFiniteExact width F)
    (run : evaluateHOLFiniteState {initialized with clock := fuel} (.call none next []) = (result,post)) :
    ∃ final, evaluateHOLFiniteState {s with clock := fuel + 1} (.call none start []) = (result,final) ∧
      final.ffi = post.ffi := by
  have same := SemInitSupport.step s initialized start next body functionBody params shape entry function
    (pan_initializer_all_clocks s initialized body initialRun clock) fuel
  rw [run] at same
  refine ⟨(evaluateHOLFiniteState {s with clock := fuel + 1} (.call none start [])).2,?_,same.2⟩
  exact Prod.ext same.1 rfl

#print axioms pan_initializer_all_clocks
#print axioms pan_init_call_one_clock
end InitECandidate.Runtime
