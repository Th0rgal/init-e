import InitECandidate.Runtime.AllocationFree
import Flapjack.Compiler.Backend.StackAlloc.Proofs.CompCorrect.Defs

namespace InitECandidate.Runtime.StackAlloc
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemStateOps Flapjack.StackSemEvaluate
open Flapjack.Compiler.Backend.StackAlloc.CompCorrect

/-- All callable procedures, including any oracle-installed code, satisfy the
syntax certificate. This is an explicit runtime invariant, not a consequence
of the initial code certificate alone. -/
structure FreeState {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) : Prop where
  code : ∀ k p, sptLookup k s.code = some p → allocationFree p = true
  oracle : ∀ n k p, (k, p) ∈ (s.compileOracle n).2.1 → allocationFree p = true

/-- The actual evaluator can only extend code from the certified oracle. -/
theorem FreeState.of_evaluate {width : Nat} [NeZero width] {C F : Type}
    {p : HolProg width} {s t : StackSemStateFiniteExact width C F}
    {r : Option (StackSemResult width)}
    (run : evaluate (p, s) = (r, t)) (free : FreeState s) : FreeState t := by
  obtain ⟨count, oracle, code, _⟩ :=
    StackProps.EvaluateCodeBitmaps.evaluateCodeBitmaps p s r t run
  constructor
  · intro key body lookup
    rw [code] at lookup
    rcases sptLookup_foldl_sptUnion _ _ _ _ lookup with old | ⟨tree, member, lookup⟩
    · exact free.code key body old
    · obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
      rw [sptLookup_sptFromAList] at lookup
      exact free.oracle index key body (sptAListLookup_mem _ _ _ lookup)
  · intro n key body member
    rw [oracle] at member
    exact free.oracle (n + count) key body member

theorem FreeState.decClock {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} (free : FreeState s) : FreeState (decClock s) :=
  ⟨free.code, free.oracle⟩

theorem FreeState.setVar {width : Nat} [NeZero width] {C F : Type}
    {s : StackSemStateFiniteExact width C F} (free : FreeState s) (reg : Nat) (v : WordLocW width) :
    FreeState (Flapjack.StackSemStateOps.setVar reg v s) := ⟨free.code, free.oracle⟩

#print axioms FreeState.of_evaluate
end InitECandidate.Runtime.StackAlloc
