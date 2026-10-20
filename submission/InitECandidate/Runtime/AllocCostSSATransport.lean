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

#print axioms wordPathWork_mustTerminate_variant
#print axioms wordPathWork_seq_variant
#print axioms wordPathWork_ite_variant

end InitECandidate.Runtime.FineCost
