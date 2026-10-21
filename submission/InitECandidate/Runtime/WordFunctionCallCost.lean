import InitECandidate.Runtime.WordFunctionExecutionCost
import InitECandidate.Runtime.WordOptimizerPrice
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

theorem function_tail_call_cost {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (function : Nat)
    (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (hg : WordSemStateFiniteExact.getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (hf : wordSemFindCode dest xs s.code s.stackSize = some (args1, prog, ss)) (hz : s.clock ≠ 0) :
    wordFunctionExecutionCost price function (.call none dest args none) s =
      price function (.call none dest args none) s + wordFunctionExecutionCost price ((wordCallLabel dest xs).getD 0) prog (callEnv args1 ss (decClock s)) := by
  rw [wordFunctionExecutionCost]
  simp only [hg, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, dif_neg hz]

/-- Work after a returning call's callee: the return continuation or handler. -/
noncomputable def wordFunctionRetCont {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (function : Nat)
    (n : List Nat) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) :
    Option (WordSemResult 64) → WordSemStateFiniteExact 64 C F → Nat
  | some (.result location returned), middle =>
    if location ≠ .loc l1 l2 ∨ returned.length ≠ n.length then 0 else
      match popEnv middle with
      | none => 0
      | some popped =>
        if sptDomainEqUnion popped.locals envs.1 envs.2 then
          wordFunctionExecutionCost price function retCode (setVars n returned popped)
        else 0
  | some (.exception location value), middle =>
    match handler with
    | none => 0
    | some (reg, handlerCode, h1, h2) =>
      if location ≠ .loc h1 h2 then 0 else
      if sptDomainEqUnion middle.locals envs.1 envs.2 then
        wordFunctionExecutionCost price function handlerCode (setVar reg value middle)
      else 0
  | _, _ => 0

theorem function_ret_call_cost {C F : Type} (price : Nat → WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (function : Nat)
    (n : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (hg : WordSemStateFiniteExact.getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize = some (args1, prog, ss))
    (hdc : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (hce : wordSemCutEnvs names s.locals = some envs) (hz : s.clock ≠ 0)
    (rc : Option (WordSemResult 64)) (s2 : WordSemStateFiniteExact 64 C F)
    (hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) = (rc, s2)) :
    wordFunctionExecutionCost price function (.call (some (n, names, retCode, l1, l2)) dest args handler) s =
      price function (.call (some (n, names, retCode, l1, l2)) dest args handler) s +
        wordFunctionExecutionCost price ((wordCallLabel dest (.loc l1 l2 :: xs)).getD 0) prog (callEnv args1 ss (pushEnv envs handler (decClock s))) +
        wordFunctionRetCont price function n retCode l1 l2 handler envs rc s2 := by
  rw [wordFunctionExecutionCost]
  simp only [hg, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce, dif_neg hz]
  have hfc : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s))) (rc, s2) = (rc, s2) := by
    rw [← hcv]; exact fix_clock_evaluate _ _
  rw [hcv, hfc]
  rcases rc with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp [wordFunctionRetCont]
  split
  · rfl
  · rcases hp : popEnv s2 with _ | p <;> simp
  rcases handler with _ | ⟨reg, hc, h1, h2⟩ <;> simp

#print axioms function_ret_call_cost

#print axioms function_tail_call_cost
end InitECandidate.Runtime.FineCost
