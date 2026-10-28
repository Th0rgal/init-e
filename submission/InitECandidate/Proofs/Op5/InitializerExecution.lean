import InitECandidate.Proofs.Op5.InitializerStores
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm

variable {width : Nat} [NeZero width] {C F : Type}

/-- The complete unchanged initializer runs with scratch in its store-list
frame. Its original register outcomes and complete frame assertion are retained,
and every scratch word is preserved. The input assertion describes ownership
after the terminal stack-slot write; that write is handled by writeWord. -/
theorem runInitCode_preserves_arena (generateGc : Bool) (maxHeap k : Nat) (s : StackSemStateFiniteExact width C F)
    (p2 p3 p4 bitmapPointer : BitVec width) (v1 v2 v3 v4 : WordLocW width)
    (good : goodDimindex width) (k8 : 8 ≤ k)
    (read2 : s.regs.lookup 2 = some (.word p2)) (read3 : s.regs.lookup 3 = some (.word p3))
    (read4 : s.regs.lookup 4 = some (.word p4))
    (domain : ∀ i, i < 5 → s.mdomain (p2 + BitVec.ofNat width i * bytesInWord width) = true)
    (load0 : s.memory p2 = .word bitmapPointer)
    (load1 : s.memory (p2 + bytesInWord width) = v1)
    (load2 : s.memory (p2 + bytesInWord width + bytesInWord width) = v2)
    (load3 : s.memory (p2 + bytesInWord width + bytesInWord width + bytesInWord width) = v3)
    (load4 : s.memory (p2 + bytesInWord width + bytesInWord width + bytesInWord width +
      bytesInWord width) = v4)
    (lastDomain : s.mdomain (p4 - bytesInWord width) = true)
    (entry : sptDomain s.code 1)
    (ys : List (WordLocW width)) (arena : BitVec width → Prop)
    (remainder : ((BitVec width × WordLocW width) → Prop) → Prop)
    (ylen : ys.length = storeList.length)
    (storeHeap : SetSep.star
      (Misc.wordList (roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
        (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap))) ys)
      (SetSep.star (memoryHOL s.memory arena) remainder)
      (SetSep.fun2Set ((fun key => if key = p4 - bytesInWord width then .word 0 else s.memory key),
        fun a => s.mdomain a = true))) :
    let reg3 := roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
      (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap))
    let half := (reg3 - p2) >>> (1 : Nat)
    ∃ t : StackSemStateFiniteExact width C F,
      StackSemEvaluate.evaluate (initCode generateGc maxHeap k, s) = (none, t) ∧
      t = {s with memory := t.memory, regs := t.regs} ∧
      t.regs.lookup 0 = some (.loc 1 0) ∧ t.regs.lookup 1 = some v4 ∧
      t.regs.lookup 2 = some (.word (p2 + half)) ∧
      t.regs.lookup 3 = some (.word (bitmapPointer >>> wordShiftAmount width)) ∧
      t.regs.lookup 4 = some v1 ∧ t.regs.lookup 5 = some (.word half) ∧
      t.regs.lookup 6 = some v2 ∧ t.regs.lookup 7 = some v3 ∧
      t.regs.lookup k = some (.word (p4 - bytesInWord width)) ∧
      t.regs.lookup (k + 1) =
        some (.word (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)) ∧
      t.regs.lookup (k + 2) = some (.word p2) ∧
      (∀ r, 8 ≤ r → r ≠ k → r ≠ k + 1 → r ≠ k + 2 → t.regs.lookup r = s.regs.lookup r) ∧
      SetSep.star
        (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc k)).map
          (MemVal.memVal t.regs))) (SetSep.star (memoryHOL s.memory arena) remainder)
        (SetSep.fun2Set (t.memory, fun a => s.mdomain a = true)) ∧
      (∀ a, arena a → t.memory a = s.memory a) := by
  intro reg3 half
  obtain ⟨t,run,shape,h0,h1,h2,h3,h4,h5,h6,h7,hk,hk1,hk2,rest,heap⟩ :=
    runInitCode generateGc maxHeap k s p2 p3 p4 bitmapPointer v1 v2 v3 v4 good k8
      read2 read3 read4 domain load0 load1 load2 load3 load4 lastDomain entry ys
      (SetSep.star (memoryHOL s.memory arena) remainder) ylen storeHeap
  exact ⟨t,run,shape,h0,h1,h2,h3,h4,h5,h6,h7,hk,hk1,hk2,rest,heap,
    initializer_arena_read reg3 _ s.memory t.memory arena _ remainder heap⟩

#print axioms runInitCode_preserves_arena
end InitE.Op5
