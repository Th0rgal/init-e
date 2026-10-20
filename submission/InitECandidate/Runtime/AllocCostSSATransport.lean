/-
# Work transport along permuted stacks (`PERM_STACK`)

`wordPathWork` counts the executed nodes of the selected path.  The SSA
correctness relation fixes the source permutation existentially, so the executed
work must be shown invariant when the source state's `permute` oracle and stack
roots are replaced by a `PERM_STACK`-related variant.  This module proves the
first slice of that transport: the leaf (`mustTerminate`) case, the sequence
step and the conditional step.  The step lemmas are stated with the transported
work of the sub-programs as explicit hypotheses, i.e. exactly the premises a
termination-measure recursion (mirroring `WordSemStateFiniteExact.swap_aux`)
passes to its induction hypotheses; the actual sub-runs are those of the real
program, so no whole-program evaluation premise is assumed.

The remaining step cases (`.loop`, `.call`) and the recursive driver are the
next slice; the SSA call transfer already leaves only this permute bookkeeping.
-/
import InitECandidate.Runtime.AllocCostSSABodyWork
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.PermuteSwapStack

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact Flapjack.WordProps
open InitECandidate.Runtime.WordToStack
set_option maxHeartbeats 400000


theorem wordPathWork_mustTerminate_variant{C F : Type} (c : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64)) :
    wordPathWork (.mustTerminate c) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork (.mustTerminate c) s := by
  rw [wordPathWork, wordPathWork]
  all_goals simp

theorem wordPathWork_seq_variant{C F : Type}
    (first second : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64))
    (res : Option (WordSemResult 64)) (s1 : WordSemStateFiniteExact 64 C F)
    (k1 : Nat → Nat → Nat) (xs1 : List (WordSemStackFrame 64))
    (runS : evaluate first s = (res, s1))
    (runT : evaluate first ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = (res, { s1 with permute := k1, stack := xs1 }))
    (ih1 : wordPathWork first ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork first s)
    (ih2 : wordPathWork second ({ s1 with permute := k1, stack := xs1 } :
      WordSemStateFiniteExact 64 C F) = wordPathWork second s1) :
    wordPathWork (.seq first second) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork (.seq first second) s := by
  rw [wordPathWork_seq, wordPathWork_seq]
  rw [runT, runS]
  rw [ih1]
  cases res with
  | none => dsimp only; rw [ih2]
  | some r => rfl

theorem wordPathWork_ite_variant{C F : Type}
    (cmp : Cmp) (reg : Nat) (operand : WordRegImm (BitVec 64))
    (first second : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F)
    (k : Nat → Nat → Nat) (xs : List (WordSemStackFrame 64))
    (ih1 : wordPathWork first ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork first s)
    (ih2 : wordPathWork second ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork second s) :
    wordPathWork (.ite cmp reg operand first second) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) =
      wordPathWork (.ite cmp reg operand first second) s := by
  have hv : getVar reg ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = getVar reg s := rfl
  have hi : getVarImm operand ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = getVarImm operand s := by
    cases operand <;> rfl
  rw [wordPathWork, wordPathWork, hv, hi]
  cases hx : getVar reg s with
  | none => simp only [hx]
  | some x =>
    cases hy : getVarImm operand s with
    | none => simp only [hx, hy]
    | some y =>
      cases hc : wordSemWordCmp cmp x y with
      | none => simp only [hx, hy, hc]
      | some b =>
        cases b with
        | true => simp only [hx, hy, hc]; rw [ih1]
        | false => simp only [hx, hy, hc]; rw [ih2]


/-- Non-returning call step: the same `getVars`/`findCode` selection is read at
the variant state, and the compiled-free call node plus the callee body's
transported work at the literal `callEnv` entry gives the same total. -/
theorem wordPathWork_call_none_variant {C F : Type}
    (dest : Option Nat) (args : List Nat)
    (s : WordSemStateFiniteExact 64 C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame 64))
    (values : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (get : getVars args s = some values)
    (hbad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) values) s.code s.stackSize =
      some (args1, prog, ss))
    (hz : s.clock ≠ 0)
    (ih : wordPathWork prog (callEnv args1 ss (decClock ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F))) = wordPathWork prog (callEnv args1 ss (decClock s))) :
    wordPathWork (.call none dest args none) ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = wordPathWork (.call none dest args none) s := by
  have hgetT : getVars args ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = some values := by
    rw [getVars_swap]; exact get
  have hfindT : wordSemFindCode dest
      (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL ×
        WordLangProgHOL (BitVec 64) × Nat × Nat)) values)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).stackSize =
      some (args1, prog, ss) := find
  have hzT : ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).clock ≠ 0 := hz
  rw [wordPathWork_call_none_body_eq dest args ({ s with permute := k, stack := xs })
      values args1 prog ss hgetT hbad hfindT hzT,
    wordPathWork_call_none_body_eq dest args s values args1 prog ss get hbad find hz, ih]

/-- Returning call, `result` branch: the variant reads the same arguments,
uses the same code and cut environments, the body's actual transported run
returns the same result, its environment pops to a `PERM_STACK`-related frame,
and both the body work and the return-handler work transfer. -/
theorem wordPathWork_call_returning_result_variant {C F : Type}
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (k : Nat → Nat → Nat)
    (xs : List (WordSemStackFrame 64))
    (vals0 : List (WordLocW 64)) (args1 : List (WordLocW 64))
    (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (location : WordLocW 64) (returned : List (WordLocW 64))
    (middle middleX : WordSemStateFiniteExact 64 C F)
    (popped : WordSemStateFiniteExact 64 C F)
    (k3 : Nat → Nat → Nat) (xs3 : List (WordSemStackFrame 64))
    (get : getVars args s = some vals0)
    (hbad : wordSemBadDestArgs dest args = false)
    (find : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0) s.code s.stackSize =
      some (args1, prog, ss))
    (dom : ¬ sptDomainEmpty names.1) (nodup : values.Nodup)
    (cut : wordSemCutEnvs names s.locals = some envs)
    (clock : s.clock ≠ 0)
    (runS : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) =
      (some (.result location returned), middle))
    (popS : popEnv middle = some popped)
    (locEq : location = .loc l1 l2)
    (lenEq : returned.length = values.length)
    (domUnion : sptDomainEqUnion popped.locals envs.1 envs.2)
    (runT : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      (some (.result location returned), middleX))
    (popT : popEnv middleX = some ({ popped with permute := k3, stack := xs3 } :
      WordSemStateFiniteExact 64 C F))
    (ihBody : wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F)))) =
      wordPathWork prog (callEnv args1 ss (pushEnv envs handler (decClock s))))
    (ihRet : wordPathWork retCode ({ setVars values returned popped with
      permute := k3, stack := xs3 } : WordSemStateFiniteExact 64 C F) =
      wordPathWork retCode (setVars values returned popped)) :
    wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F) =
      wordPathWork (.call (some (values, names, retCode, l1, l2)) dest args handler) s := by
  have hgetT : getVars args ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F) = some vals0 := by
    rw [getVars_swap]; exact get
  have hfindT : wordSemFindCode dest
      (wordSemAddRetLoc (some (values, names, retCode, l1, l2)) vals0)
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).code
      ({ s with permute := k, stack := xs } : WordSemStateFiniteExact 64 C F).stackSize =
      some (args1, prog, ss) := find
  have hcutT : wordSemCutEnvs names ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).locals = some envs := cut
  have hclockT : ({ s with permute := k, stack := xs } :
      WordSemStateFiniteExact 64 C F).clock ≠ 0 := clock
  have hdomUnionT : sptDomainEqUnion ({ popped with permute := k3, stack := xs3 } :
      WordSemStateFiniteExact 64 C F).locals envs.1 envs.2 := domUnion
  have hsv : setVars values returned ({ popped with permute := k3, stack := xs3 } :
      WordSemStateFiniteExact 64 C F) =
      ({ setVars values returned popped with permute := k3, stack := xs3 } :
        WordSemStateFiniteExact 64 C F) := rfl
  rw [wordPathWork_call_returning_result values names retCode l1 l2 dest args handler
      ({ s with permute := k, stack := xs }) middleX
      ({ popped with permute := k3, stack := xs3 }) vals0 envs args1 prog ss location returned
      hgetT hbad hfindT dom nodup hcutT hclockT (by rw [fix_clock_evaluate]; exact runT)
      popT locEq lenEq hdomUnionT,
    wordPathWork_call_returning_result values names retCode l1 l2 dest args handler s middle
      popped vals0 envs args1 prog ss location returned get hbad find dom nodup cut clock
      (by rw [fix_clock_evaluate]; exact runS) popS locEq lenEq domUnion]
  rw [hsv, ihBody, ihRet]

#print axioms wordPathWork_mustTerminate_variant
#print axioms wordPathWork_seq_variant
#print axioms wordPathWork_ite_variant
#print axioms wordPathWork_call_none_variant
#print axioms wordPathWork_call_returning_result_variant

end InitECandidate.Runtime.FineCost
