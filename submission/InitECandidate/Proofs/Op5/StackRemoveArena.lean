import InitECandidate.Proofs.Op5.HeapExtension
import Flapjack.Compiler.Backend.StackRemove.Proofs.StateRelation
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitReduce

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove

open Classical in
/-- Add ordinary scratch ownership without changing registers, memory values,
code, callbacks, stack abstraction, or compiler resource bounds. -/
noncomputable def withArena {width : Nat} [NeZero width] {C F : Type}
    (arena : BitVec width → Prop) (s : StackSemStateFiniteExact width C F) :=
  {s with mdomain := fun a => s.mdomain a || decide (arena a)}

/-- Lifting the actual StackRemove simulation relation, including its five
heap assertions. Scratch is separate from the old target heap, whose ownership
already includes bitmap/data buffers, store slots and stack cells. -/
theorem stackRemove_stateRel_withArena {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F) (arena : BitVec width → Prop)
    (rel : stateRelHOL jump bounds pointer source target)
    (disjoint : ∀ a, ¬ (arena a ∧ target.mdomain a = true))
    (agree : ∀ a, arena a → source.memory a = target.memory a) :
    stateRelHOL jump bounds pointer (withArena arena source) (withArena arena target) := by
  classical
  simp only [stateRelHOL, withArena] at rel ⊢
  rcases rel with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25,h26⟩
  refine ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25,?_⟩
  split at h26
  · rename_i base _heq
    obtain ⟨hb,hlo,hhi,hreg,hheap⟩ := h26
    refine ⟨hb,hlo,hhi,hreg,?_⟩
    simp only [Bool.or_eq_true,decide_eq_true_eq]
    simp only [← SetSep.starAssoc] at hheap ⊢
    exact memory_frame_extend source.memory target.memory _ _ arena _ hheap disjoint agree
  · exact h26

/-- The initializer reduction with scratch retains the original reducer's
entire state, adding only the independent ordinary memory domain. -/
noncomputable def initReduceWithArena {width : Nat} [NeZero width] {C F : Type}
    (arena : BitVec width → Prop)
    (gc jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (code : Spt (Compiler.Backend.StackLang.HolProg width)) (bitmaps : List (BitVec width))
    (dataSpace : Nat)
    (oracle : Nat → C × List (Nat × Compiler.Backend.StackLang.HolProg width) × List (BitVec width))
    (source : StackSemStateFiniteExact width C F) :=
  withArena arena (Proofs.InitReduce.initReduce gc jump bounds pointer code bitmaps dataSpace oracle source)

#print axioms stackRemove_stateRel_withArena
end InitE.Op5
