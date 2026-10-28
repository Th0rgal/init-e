import InitECandidate.Proofs.Op5.Separation
import Flapjack.Compiler.Backend.StackRemove.Proofs.StoreListCodeThm

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Values in the arena part of an initializer frame remain readable, even
when the generated store-list changes every value in its own word list. -/
theorem initializer_arena_read {width : Nat} [NeZero width]
    (base : BitVec width) (values : List (WordLocW width))
    (scratch memory : BitVec width → WordLocW width)
    (arena domain : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (heap : SetSep.star (Misc.wordList base values)
      (SetSep.star (memoryHOL scratch arena) frame) (SetSep.fun2Set (memory,domain))) :
    ∀ a, arena a → memory a = scratch a := by
  have reordered : SetSep.star (memoryHOL scratch arena)
      (SetSep.star (Misc.wordList base values) frame) (SetSep.fun2Set (memory,domain)) := by
    rw [SetSep.starAssoc, SetSep.starComm (memoryHOL scratch arena), ← SetSep.starAssoc]
    exact heap
  intro a ha
  exact (MemoryReads.memoryFun2SetImpRead scratch memory arena domain _ a ⟨reordered,ha⟩).2

/-- The initializer's first memory write preserves scratch ownership. The
terminal stack slot is separated from the store list and arena in the input;
no pointwise preservation premise is needed. -/
theorem initializer_terminal_write {width : Nat} [NeZero width]
    (last base : BitVec width) (oldLast : WordLocW width)
    (values : List (WordLocW width)) (memory : BitVec width → WordLocW width)
    (arena domain : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (heap : SetSep.star (SetSep.one (last,oldLast))
      (SetSep.star (Misc.wordList base values) (SetSep.star (memoryHOL memory arena) frame))
      (SetSep.fun2Set (memory,domain))) :
    SetSep.star (Misc.wordList base values)
      (SetSep.star (memoryHOL memory arena) (SetSep.star frame (SetSep.one (last,.word 0))))
      (SetSep.fun2Set ((fun a => if a = last then .word 0 else memory a),domain)) := by
  have written := StoreListCodeThm.writeWord (.word 0) oldLast last _ memory domain heap
  simpa only [← SetSep.starAssoc] using written

/-- Actual execution of the unchanged initializer store-list preserves scratch.
All original execution guards are retained; no poststate or execution result
is assumed. The initial separation assertion derives all alias exclusions. -/
theorem storeListCode_preserves_arena {width : Nat} [NeZero width] {C F : Type}
    (addressReg tempReg : Nat) (xs : List (BitVec width ⊕ Nat))
    (s : StackSemStateFiniteExact width C F) (base : BitVec width)
    (scratch : BitVec width → WordLocW width) (arena : BitVec width → Prop)
    (frame : ((BitVec width × WordLocW width) → Prop) → Prop)
    (oldValues : List (WordLocW width))
    (heap : SetSep.star (Misc.wordList base oldValues)
      (SetSep.star (memoryHOL scratch arena) frame)
      (SetSep.fun2Set (s.memory, fun a => s.mdomain a = true)))
    (lengths : oldValues.length = xs.length) (distinct : addressReg ≠ tempReg)
    (read : StackSemStateOps.getVar addressReg s = some (.word base))
    (present : s.regs.lookup tempReg ≠ none)
    (guards : ∀ x ∈ xs, ∀ n, Sum.inr n = x →
      n ≠ addressReg ∧ n ≠ tempReg ∧ s.regs.lookup n ≠ none) :
    ∃ r1 m1,
      StackSemEvaluate.evaluate (storeListCode addressReg tempReg xs,s) =
        (none,{s with memory := m1, regs := (s.regs.updateListEq
          [(addressReg,.word (base + bytesInWord width * BitVec.ofNat width xs.length)),
            (tempReg,r1)])}) ∧
      (∀ a, arena a → m1 a = scratch a) := by
  obtain ⟨r1,m1,hheap,run⟩ := StoreListCodeThm.storeListCodeThm addressReg tempReg xs s base
    (SetSep.star (memoryHOL scratch arena) frame) oldValues s.memory
    (fun a => s.mdomain a = true) ⟨heap,rfl,rfl,lengths,distinct,read,present,guards⟩
  exact ⟨r1,m1,run,initializer_arena_read base _ scratch m1 arena _ frame hheap⟩

#print axioms initializer_arena_read
#print axioms storeListCode_preserves_arena
end InitE.Op5
