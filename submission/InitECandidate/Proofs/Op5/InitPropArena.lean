import InitECandidate.Proofs.Op5.StackRemoveArena
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitProp

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Every pinned initialized-state clause is retained; scratch is owned
separately from the two heap regions in the final separation assertion. -/
def initPropWithArena {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap dataSpace : Nat) (limits : Nat × Nat)
    (source : StackSemStateFiniteExact width C F) (arena : BitVec width → Prop) : Prop :=
  ∃ (current other bitmapBase : BitVec width) (length : Nat),
    source.store.lookup .currHeap = some (.word current) ∧
    source.store.lookup .nextFree = some (.word current) ∧
    source.store.lookup .triggerGC = some (.word (if generateGc then current else other)) ∧
    source.store.lookup .endOfHeap = some (.word other) ∧
    source.store.lookup .otherHeap = some (.word other) ∧
    source.store.lookup .bitmapBase = some (.word bitmapBase) ∧
    source.store.lookup .heapLength =
      some (.word (BitVec.ofNat width length * bytesInWord width)) ∧
    source.store.lookup .progStart = some (.word 0) ∧
    source.store.lookup .allocSize = some (.word 0) ∧
    source.store.lookup .globals = some (.word 0) ∧
    source.store.lookup .globReal = some (.word current) ∧
    source.store.lookup .handler = some (.word 0) ∧
    source.store.lookup .genStart = some (.word 0) ∧
    source.store.lookup .codeBuffer = some (.word source.codeBuffer.position) ∧
    source.store.lookup .codeBufferEnd =
      some (.word (source.codeBuffer.position + BitVec.ofNat width source.codeBuffer.spaceLeft)) ∧
    source.store.lookup .bitmapBuffer = some (.word source.dataBuffer.position) ∧
    source.store.lookup .bitmapBufferEnd =
      some (.word (source.dataBuffer.position +
        bytesInWord width * BitVec.ofNat width source.dataBuffer.spaceLeft)) ∧
    StackHeapLimitOk.stackHeapLimitOk source limits ∧
    source.codeBuffer.buffer = [] ∧ source.dataBuffer.buffer = [] ∧
    source.useStack = true ∧ source.useStore = true ∧
    source.regs.lookup 0 = some (.loc 1 0) ∧
    source.bitmaps.length + dataSpace + 1 < 2 ^ width ∧
    source.stack.length < 2 ^ width ∧
    other = current + bytesInWord width * BitVec.ofNat width length ∧
    holByteAligned current = true ∧
    holLast source.stack = .word 0 ∧
    source.stack.length = source.stackSpace + 1 ∧
    source.stack.length * (width / 8) < 2 ^ width ∧
    length + length ≤ maxHeap ∧
    SetSep.star
      (SetSep.star (Misc.wordListExists current length) (Misc.wordListExists other length))
      (memoryHOL source.memory arena)
      (SetSep.fun2Set (source.memory, fun address => source.mdomain address = true))


/-- Generic assertion extension used to carry the initializer heap predicate
alongside scratch, retaining exact ownership of the complete memory graph. -/
theorem assertion_arena_extend {A V : Type} (m : A → V) (domain arena : A → Prop)
    (P : ((A × V) → Prop) → Prop)
    (old : P (SetSep.fun2Set (m,domain)))
    (disjoint : ∀ a, ¬ (domain a ∧ arena a)) :
    SetSep.star P (memoryHOL m arena)
      (SetSep.fun2Set (m,fun a => domain a ∨ arena a)) := by
  have split := congrFun (memory_union_split m domain arena disjoint)
    (SetSep.fun2Set (m,fun a => domain a ∨ arena a))
  have h : SetSep.star (memoryHOL m domain) (memoryHOL m arena)
      (SetSep.fun2Set (m,fun a => domain a ∨ arena a)) := by
    rw [← split]
    rfl
  obtain ⟨left,right,parts,hl,hr⟩ := h
  change left = SetSep.fun2Set (m,domain) at hl
  exact ⟨left,right,parts,hl ▸ old,hr⟩

/-- The initialized-state predicate now retains the scratch frame rather than
forcing the enlarged ordinary domain to equal only two contiguous heaps. -/
theorem initProp_withArena {width : Nat} [NeZero width] {C F : Type}
    (gc : Bool) (maxHeap dataSpace : Nat) (limits : Nat × Nat)
    (source : StackSemStateFiniteExact width C F) (arena : BitVec width → Prop)
    (old : InitProp.initProp gc maxHeap dataSpace limits source)
    (disjoint : ∀ a, ¬ (source.mdomain a = true ∧ arena a)) :
    initPropWithArena gc maxHeap dataSpace limits (withArena arena source) arena := by
  classical
  obtain ⟨current,other,bitmap,len,h⟩ := old
  refine ⟨current,other,bitmap,len,?_⟩
  simp only [withArena, Bool.or_eq_true,decide_eq_true_eq]
  rcases h with ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,h32⟩
  exact ⟨h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16,
    h17,h18,h19,h20,h21,h22,h23,h24,h25,h26,h27,h28,h29,h30,h31,
    assertion_arena_extend source.memory _ arena _ h32 disjoint⟩

#print axioms assertion_arena_extend
#print axioms initProp_withArena
end InitE.Op5
