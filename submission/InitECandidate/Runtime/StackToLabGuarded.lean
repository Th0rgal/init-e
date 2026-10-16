import InitECandidate.Runtime.StackToLabIf
import Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect.Guarded

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackToLab.Proofs.CodeInstalled
open Flapjack.Compiler.Backend.StackToLab.Proofs.StateRel
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenHelpers
open Flapjack.Compiler.Backend.StackToLab.Proofs.FlattenCorrect
open Flapjack.Compiler.Backend.StackToLab.Proofs

section
variable {width : Nat} [NeZero width] {C F : Type}
theorem flattenSkip_bounded (s1 : StackSemStateFiniteExact width C F) :
    BoundedFlattenProp (.skip : HolProg width) s1 0 := by
  rintro t r s2 n l cs bs t1 ⟨ev, _, rel, _, _, _⟩
  rw [StackSemEvaluate.evaluate_skip] at ev
  cases ev
  exact boundedFlattenConclStay 0 rel
    (by simp [Flapjack.Compiler.Backend.StackToLab.flattenHOL, appListAppendList])
/-- Shared shape: the clause returns `SOME Error` from the state relation. -/
private theorem boundedGuarded {prog : HolProg width} {s1 : StackSemStateFiniteExact width C F}
    (h : ∀ (t : Flapjack.Compiler.Backend.LabSem.State width C F), stateRel s1 t →
      (StackSemEvaluate.evaluate (prog, s1)).1 = some .error) :
    BoundedFlattenProp prog s1 0 := by
  rintro t r s2 n l cs bs t1 ⟨ev, nerr, rel, -⟩
  have := h t1 rel
  rw [ev] at this
  exact absurd this nerr

theorem flattenGuardedAlloc (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedFlattenProp (.alloc k : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_alloc]; simp [(relNoStack rel).2.2]

theorem flattenGuardedStoreConsts (s1 : StackSemStateFiniteExact width C F)
    (a b : Nat) (stub : Option Nat) :
    BoundedFlattenProp (.storeConsts a b stub : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_storeConsts]; simp [(relNoStack rel).2.1]

theorem flattenGuardedGet (s1 : StackSemStateFiniteExact width C F) (v : Nat)
    (name : StoreName) : BoundedFlattenProp (.get v name : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_get]; simp [(relNoStack rel).2.1]

theorem flattenGuardedSet (s1 : StackSemStateFiniteExact width C F) (v : Nat)
    (name : StoreName) : BoundedFlattenProp (.set name v : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_set]; simp [(relNoStack rel).2.1]

theorem flattenGuardedOpCurrHeap (s1 : StackSemStateFiniteExact width C F)
    (op : Compiler.Encoders.Asm.HolBinop) (v src : Nat) :
    BoundedFlattenProp (.opCurrHeap op v src : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_opCurrHeap]; simp [(relNoStack rel).2.1]

theorem flattenGuardedStackAlloc (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedFlattenProp (.stackAlloc k : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackAlloc]; simp [(relNoStack rel).1]

theorem flattenGuardedStackFree (s1 : StackSemStateFiniteExact width C F) (k : Nat) :
    BoundedFlattenProp (.stackFree k : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackFree]; simp [(relNoStack rel).1]

theorem flattenGuardedStackLoad (s1 : StackSemStateFiniteExact width C F) (r k : Nat) :
    BoundedFlattenProp (.stackLoad r k : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackLoad]; simp [(relNoStack rel).1]

theorem flattenGuardedStackLoadAny (s1 : StackSemStateFiniteExact width C F) (r rn : Nat) :
    BoundedFlattenProp (.stackLoadAny r rn : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackLoadAny]; simp [(relNoStack rel).1]

theorem flattenGuardedStackStore (s1 : StackSemStateFiniteExact width C F) (r k : Nat) :
    BoundedFlattenProp (.stackStore r k : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackStore]; simp [(relNoStack rel).1]

theorem flattenGuardedStackStoreAny (s1 : StackSemStateFiniteExact width C F) (r rn : Nat) :
    BoundedFlattenProp (.stackStoreAny r rn : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackStoreAny]; simp [(relNoStack rel).1]

theorem flattenGuardedStackGetSize (s1 : StackSemStateFiniteExact width C F) (r : Nat) :
    BoundedFlattenProp (.stackGetSize r : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackGetSize]; simp [(relNoStack rel).1]

theorem flattenGuardedStackSetSize (s1 : StackSemStateFiniteExact width C F) (r : Nat) :
    BoundedFlattenProp (.stackSetSize r : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_stackSetSize]; simp [(relNoStack rel).1]

theorem flattenGuardedBitmapLoad (s1 : StackSemStateFiniteExact width C F) (r v : Nat) :
    BoundedFlattenProp (.bitmapLoad r v : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_bitmapLoad]; simp [(relNoStack rel).1]

theorem flattenGuardedDataBufferWrite (s1 : StackSemStateFiniteExact width C F) (r1 r2 : Nat) :
    BoundedFlattenProp (.dataBufferWrite r1 r2 : HolProg width) s1 0 :=
  boundedGuarded fun t rel => by
    rw [StackSemEvaluate.evaluate_dataBufferWrite]; simp [(relNoStack rel).1]

end
end InitECandidate.Runtime.StackToLab
#print axioms InitECandidate.Runtime.StackToLab.flattenSkip_bounded
#print axioms InitECandidate.Runtime.StackToLab.flattenGuardedAlloc
