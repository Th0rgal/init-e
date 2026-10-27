import InitECandidate.Proofs.Op5.InitializerExecution
import Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeThm
open Flapjack.Compiler.Backend.StackRemove.Proofs.InitCodeCorrect

/-- The pinned initializer precondition, with an independently owned scratch
heap. All pointer, register, header, alignment and capacity guards are retained. -/
def initCodePreWithArena {width : Nat} [NeZero width] {C F : Type}
    (pointer : Nat) (bitmaps : List (BitVec width)) (dataSpace : Nat)
    (source : StackSemStateFiniteExact width C F) (arena : BitVec width → Prop) : Prop :=
  ∃ ptr2 ptr3 ptr4 bitmapPointer : BitVec width,
    goodDimindex width ∧ 8 ≤ pointer ∧ sptDomain source.code 1 ∧
    (∀ register, register = pointer ∨ register = pointer + 1 ∨ register = pointer + 2 →
      source.ffiSaveRegs register = true) ∧
    source.useStack = false ∧ source.useStore = false ∧ source.useAlloc = false ∧
    source.regs.lookup 2 = some (.word ptr2) ∧
    source.regs.lookup 3 = some (.word ptr3) ∧
    source.regs.lookup 4 = some (.word ptr4) ∧
    source.memory ptr2 = .word bitmapPointer ∧
    source.memory (ptr2 + bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    source.memory (ptr2 + 2 * bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length +
        bytesInWord width * BitVec.ofNat width dataSpace) ∧
    source.memory (ptr2 + 3 * bytesInWord width) = .word source.codeBuffer.position ∧
    source.memory (ptr2 + 4 * bytesInWord width) =
      .word (source.codeBuffer.position + BitVec.ofNat width source.codeBuffer.spaceLeft) ∧
    ptr2.toNat ≤ ptr4.toNat ∧
    (1024 * bytesInWord width).toNat ≤ (ptr4 - ptr2).toNat ∧
    holByteAligned ptr2 = true ∧ holByteAligned ptr4 = true ∧
    holByteAligned bitmapPointer = true ∧
    source.codeBuffer.buffer = [] ∧
    SetSep.star
      (SetSep.star
        (SetSep.star
        (Misc.wordList bitmapPointer (bitmaps.map WordLocW.word))
        (Misc.wordListExists
          (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) dataSpace))
        (memoryHOL source.memory arena))
      (Misc.wordListExists ptr2 ((ptr4 - ptr2).toNat / (bytesInWord width).toNat))
      (SetSep.fun2Set (source.memory, fun address => source.mdomain address = true))


/-- A successful run of the unchanged initCode is derived from the arena-framed
precondition. No execution result, scratch preservation, or initialized state
relation is supplied as a premise. -/
theorem initCodePreWithArena_run {width : Nat} [NeZero width] {C F : Type}
    (generateGc : Bool) (maxHeap pointer : Nat) (bitmaps : List (BitVec width))
    (dataSpace : Nat) (s : StackSemStateFiniteExact width C F)
    (arena : BitVec width → Prop)
    (pre : initCodePreWithArena pointer bitmaps dataSpace s arena)
    (maxOk : maxStackAlloc ≤ maxHeap) :
    ∃ t, StackSemEvaluate.evaluate (initCode generateGc maxHeap pointer,s) = (none,t) ∧
      t = {s with memory := t.memory, regs := t.regs} ∧
      (∀ a, arena a → t.memory a = s.memory a) := by
  obtain ⟨p2, p3, p4, bp, good, k8, entry, saveRegs, noStack, noStore, noAlloc, read2, read3,
    read4, mem0, mem1, mem2, mem3, mem4, le, big, al2, al4, albp, cbEmpty, heap⟩ := pre
  have a2 := (byteAligned_iff good p2).mp al2
  have a4 := (byteAligned_iff good p4).mp al4
  have bnat : (bytesInWord width).toNat = width / 8 := by
    rcases good with h | h <;> subst h <;> rfl
  have diff : (p4 - p2).toNat = p4.toNat - p2.toNat := by
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact le)]
  have big' : 1024 * (width / 8) ≤ p4.toNat - p2.toNat := by
    rw [← diff]
    have : (1024 * bytesInWord width).toNat = 1024 * (width / 8) := by
      rcases good with h | h <;> subst h <;> rfl
    omega
  have bpos : 0 < width / 8 := by rcases good with h | h <;> subst h <;> decide
  obtain ⟨adjLe, shrLe, heapLength, stackLength, regEqN, endEqN, even, heapLe, heapLow,
    stackLow⟩ := initLayout good maxHeap maxOk p2 p3 p4 le big' a2 a4
  set reg3 := roundedThird p2 (shrunkThird p2 (adjustedThird p3 (middleWord p2 p4)
    (p2 + marginWord width) (p4 - marginWord width)) (maxHeapWord width maxHeap)) with hreg3
  have regEq := addMulOfNat good p2 reg3 heapLength regEqN
  have endEq := addMulOfNat good reg3 p4 stackLength endEqN
  have count : (p4 - p2).toNat / (bytesInWord width).toNat = heapLength + stackLength := by
    rw [diff, bnat, endEqN, regEqN]
    rw [show p2.toNat + heapLength * (width / 8) + stackLength * (width / 8) - p2.toNat =
      (heapLength + stackLength) * (width / 8) by rw [Nat.add_mul]; omega]
    exact Nat.mul_div_cancel _ bpos
  rw [count] at heap
  have long : storeList.length + 1 ≤ stackLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at stackLow; omega
  obtain ⟨heapValues, storeValues, restValues, last, hlen, slen, rlen, split⟩ :=
    initHeapSplit _ p2 reg3 p4 heapLength stackLength _ _ regEq endEq long heap
  set B := SetSep.star (Misc.wordList bp (bitmaps.map WordLocW.word))
    (Misc.wordListExists (bp + bytesInWord width * BitVec.ofNat width bitmaps.length)
      dataSpace) with hB
  set A := memoryHOL s.memory arena with hA
  set P0 := SetSep.star B A with hP0
  set H := Misc.wordList p2 heapValues with hH
  set S := Misc.wordList reg3 storeValues with hS
  set R := Misc.wordList (reg3 + bytesInWord width * BitVec.ofNat width storeList.length)
    restValues with hR
  set D : BitVec width → Prop := fun a => s.mdomain a = true with hD
  -- header reads and domain
  have headerSplit : SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H (SetSep.fun2Set (s.memory, D)) := by
    rw [show SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 S) R)
      (SetSep.one (p4 - bytesInWord width, last))) H =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, last)) by ac_rfl]
    exact split
  have heapBig : 5 ≤ heapLength := by
    have : storeList.length = 48 := rfl
    simp only [maxStackAlloc] at heapLow; omega
  have domain5 : ∀ i, i < 5 →
      s.mdomain (p2 + BitVec.ofNat width i * bytesInWord width) = true := by
    intro i hi
    have := (framedListRead _ p2 heapValues s.memory D headerSplit i (by omega)).2
    rw [BitVec.mul_comm] at this
    exact this
  -- the final stack word
  have lastDomain : s.mdomain (p4 - bytesInWord width) = true := by
    obtain ⟨part, single, sub⟩ := starRightMember _ _ _ split
    have member := sub (p4 - bytesInWord width, last) (by rw [single])
    exact ((SetSep.fun2SetThm _ _ _ _).mp member).2
  have written := StoreListCodeThm.writeWord (.word 0) last (p4 - bytesInWord width)
    (SetSep.star (SetSep.star (SetSep.star P0 H) S) R) s.memory D
    (by rw [SetSep.starComm]; exact split)
  have storeHeap : SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0)))
      (SetSep.fun2Set ((fun key => if key = p4 - bytesInWord width then .word 0
        else s.memory key), D)) := by
    rw [show SetSep.star S (SetSep.star (SetSep.star (SetSep.star P0 H) R)
      (SetSep.one (p4 - bytesInWord width, .word 0))) =
      SetSep.star (SetSep.star (SetSep.star (SetSep.star P0 H) S) R)
        (SetSep.one (p4 - bytesInWord width, .word 0)) by ac_rfl]
    exact written
  obtain ⟨t, run, shape, t0, t1, t2, t3, t4, t5, t6, t7, tk, tk1, tk2, tOther, tHeap⟩ :=
    runInitCode generateGc maxHeap pointer s p2 p3 p4 bp _ _ _ _ good k8 read2 read3 read4
      domain5 mem0 rfl rfl rfl rfl lastDomain entry storeValues _ slen storeHeap
  have arenaHeap : SetSep.star A
      (SetSep.star (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
        (MemVal.memVal t.regs)))
        (SetSep.star (SetSep.star (SetSep.star B H) R)
          (SetSep.one (p4 - bytesInWord width,.word 0))))
      (SetSep.fun2Set (t.memory,D)) := by
    rw [show SetSep.star A
      (SetSep.star (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
        (MemVal.memVal t.regs)))
        (SetSep.star (SetSep.star (SetSep.star B H) R)
          (SetSep.one (p4 - bytesInWord width,.word 0)))) =
      SetSep.star (Misc.wordList reg3 ((storeList.reverse.map (storeInit generateGc pointer)).map
        (MemVal.memVal t.regs)))
        (SetSep.star (SetSep.star (SetSep.star P0 H) R)
          (SetSep.one (p4 - bytesInWord width,.word 0))) by
        dsimp only [P0]
        ac_rfl]
    exact tHeap
  refine ⟨t,run,shape,?_⟩
  intro a ha
  exact (MemoryReads.memoryFun2SetImpRead s.memory t.memory arena D _ a ⟨arenaHeap,ha⟩).2

#print axioms initCodePreWithArena_run
end InitE.Op5
