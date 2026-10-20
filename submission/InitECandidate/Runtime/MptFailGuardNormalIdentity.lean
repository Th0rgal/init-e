import InitECandidate.Runtime.MptFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A guard whose true branch calls the real original mpt_fail can complete
normally only by taking skip, regardless of condition-evaluation failure or
remaining clock. Its normal execution is therefore the identity. -/
theorem mpt_fail_guard_normal_identity {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (condition : ExpHOL 64) (errorCode : BitVec 64)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s
  (.ite condition (.call (some (none,none)) (ofString "mpt_fail") [.const errorCode]) .skip)=(none,post)) :
 post=s := by
 rw [evaluateHOLFiniteState_ite] at run
 split at run
 · split at run
   · rw [evaluateHOLFiniteState_skip] at run
     exact (Prod.mk.inj run).2.symm
   · have terminal:=evaluate_mptFail_call_terminal s (.const errorCode) errorCode code rfl
     rw [run] at terminal
     exact False.elim (terminal rfl)
 · simp at run

#print axioms mpt_fail_guard_normal_identity
end InitECandidate.Runtime
