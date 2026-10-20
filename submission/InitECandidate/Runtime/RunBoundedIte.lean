import InitECandidate.Runtime.RunBounded
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem RunBounded.ite {F : Type} (s : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64)
 {yes no : ProgHOL 64} {cost : Nat} (left : RunBounded s yes cost) (right : RunBounded s no cost) :
 RunBounded s (.ite condition yes no) cost := by
 unfold RunBounded at left right ⊢
 rw [evaluateHOLFiniteState_ite]
 split
 · split
   · exact right
   · exact left
 · simp

theorem evaluate_discard_guard_normal_locals {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (function : MlS) (arguments : List (ExpHOL 64))
 (run : evaluateHOLFiniteState s (.ite condition (.call (some (none,none)) function arguments) .skip)=(none,post)) :
 post.locals=s.locals := by
 rw [evaluateHOLFiniteState_ite] at run
 split at run
 · split at run
   · rw [evaluateHOLFiniteState_skip] at run
     exact congrArg (fun out=>out.2.locals) run.symm
   · have kept:=evaluate_discard_call_success_locals s function arguments (by rw [run])
     rw [run] at kept
     exact kept
 · cases run

#print axioms RunBounded.ite
#print axioms evaluate_discard_guard_normal_locals
end InitECandidate.Runtime
