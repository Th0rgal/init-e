import InitECandidate.Proofs.Op5.MemoryDomain
import Flapjack.Compiler.Backend.StackRemove.Proofs.MemoryWrites

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove

/-- Splitting the ordinary source heap into scratch and persistent components
uses the compiler's actual separation assertion, including infinite domains. -/
theorem memory_union_split {A V : Type} (m : A → V) (s p : A → Prop)
    (disj : ∀ a, ¬ (s a ∧ p a)) :
    memoryHOL m (fun a => s a ∨ p a) =
      SetSep.star (memoryHOL m s) (memoryHOL m p) := by
  funext heap
  apply propext
  constructor
  · intro h
    change heap = SetSep.fun2Set (m, fun a => s a ∨ p a) at h
    subst heap
    refine ⟨SetSep.fun2Set (m,s), SetSep.fun2Set (m,p), ⟨?_, ?_⟩, rfl, rfl⟩
    · funext entry
      rcases entry with ⟨a,v⟩
      simp only [SetSep.fun2SetThm]
      apply propext
      constructor
      · rintro (⟨hv, hs⟩ | ⟨hv, hp⟩)
        · exact ⟨hv, Or.inl hs⟩
        · exact ⟨hv, Or.inr hp⟩
      · rintro ⟨hv, hs | hp⟩
        · exact Or.inl ⟨hv, hs⟩
        · exact Or.inr ⟨hv, hp⟩
    · rintro ⟨a,v⟩ ⟨hs,hp⟩
      exact disj a ⟨(SetSep.fun2SetThm m s a v).mp hs |>.2,
        (SetSep.fun2SetThm m p a v).mp hp |>.2⟩
  · rintro ⟨left,right,hpart,hl,hr⟩
    change left = SetSep.fun2Set (m,s) at hl
    change right = SetSep.fun2Set (m,p) at hr
    change heap = SetSep.fun2Set (m, fun a => s a ∨ p a)
    rw [← hpart.1, hl, hr]
    funext entry
    rcases entry with ⟨a,v⟩
    simp only [SetSep.fun2SetThm]
    apply propext
    exact and_or_left.symm

open Classical in
/-- Stores in either source region preserve every compiler stack/bitmap frame.
This applies the existing StackRemove memory-write theorem to the union domain. -/
theorem twoRegion_store_frame {V : Type}
    (sl sh pl ph : Nat) (m target : BitVec 64 → V)
    (targetDomain : BitVec 64 → Prop)
    (frame : ((BitVec 64 × V) → Prop) → Prop)
    (a : BitVec 64) (v : V)
    (ha : twoRegion sl sh pl ph a) (ht : targetDomain a)
    (installed : SetSep.star (memoryHOL m (twoRegion sl sh pl ph)) frame
      (SetSep.fun2Set (target,targetDomain))) :
    SetSep.star
      (memoryHOL (fun x => if x = a then v else m x) (twoRegion sl sh pl ph)) frame
      (SetSep.fun2Set ((fun x => if x = a then v else target x),targetDomain)) := by
  classical
  have h := MemoryWrites.memoryWrite m target (twoRegion sl sh pl ph)
    targetDomain frame a v ⟨ha,ht,installed⟩
  convert h using 1
  all_goals
    congr 2
    funext x
    split <;> simp_all

#print axioms memory_union_split
#print axioms twoRegion_store_frame
end InitE.Op5
