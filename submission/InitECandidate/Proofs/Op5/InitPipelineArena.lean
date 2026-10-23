import InitECandidate.Proofs.Op5.InitSemanticsArena

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackRemove
open Flapjack.Compiler.Backend.StackRemove.Proofs

/-- Machine-side initialization assumptions with separately owned scratch. -/
def propagateTheseWithArena {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (bitmaps : List (BitVec width))
    (dataSpace : Nat) (arena : BitVec width → Prop) : Prop :=
  goodDimindex width ∧
  ∃ ptr2 ptr3 ptr4 bitmapPointer : BitVec width,
    s.regs.lookup 2 = some (.word ptr2) ∧
    s.regs.lookup 3 = some (.word ptr3) ∧
    s.regs.lookup 4 = some (.word ptr4) ∧
    s.memory ptr2 = .word bitmapPointer ∧
    s.memory (ptr2 + bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) ∧
    s.memory (ptr2 + 2 * bytesInWord width) =
      .word (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length +
        bytesInWord width * BitVec.ofNat width dataSpace) ∧
    s.memory (ptr2 + 3 * bytesInWord width) = .word s.codeBuffer.position ∧
    s.memory (ptr2 + 4 * bytesInWord width) =
      .word (s.codeBuffer.position + BitVec.ofNat width s.codeBuffer.spaceLeft) ∧
    s.codeBuffer.buffer = [] ∧
    ptr2.toNat ≤ ptr4.toNat ∧
    holByteAligned ptr2 = true ∧ holByteAligned ptr4 = true ∧
    holByteAligned bitmapPointer = true ∧
    (1024 * bytesInWord width).toNat ≤ (ptr4 - ptr2).toNat ∧
    SetSep.star
      (SetSep.star
        (SetSep.star
        (Misc.wordList bitmapPointer (bitmaps.map WordLocW.word))
        (Misc.wordListExists
          (bitmapPointer + bytesInWord width * BitVec.ofNat width bitmaps.length) dataSpace))
        (memoryHOL s.memory arena))
      (Misc.wordListExists ptr2 ((-1 * ptr2 + ptr4).toNat / (bytesInWord width).toNat))
      (SetSep.fun2Set (s.memory, fun address => s.mdomain address = true))


/-- The compiler and machine assumption bundles imply arena-aware initialization semantics. -/
theorem makeInitSemanticsWithArena {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (generateGc : Bool)
    (maxHeap pointer start : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (code : List (Nat × HolProg width)) (s2 : StackSemStateFiniteExact width C F)
    (bitmaps : List (BitVec width)) (dataSpace : Nat) (arena : BitVec width → Prop)
    (hyp : InitMake.dischargeThese jump bounds generateGc maxHeap pointer start oracle code s2 ∧
      propagateTheseWithArena s2 bitmaps dataSpace arena) :
    ∃ s1, makeInitOptWithArena generateGc maxHeap bitmaps dataSpace oracle jump bounds pointer
        (sptFromAList code) s2 arena = some s1 ∧
      (StackSemEvaluate.semantics start s1 ≠ HolBehaviour.fail →
        StackSemEvaluate.semantics 0 s2 = StackSemEvaluate.semantics start s1) := by
  obtain ⟨⟨every, oracleBound, oracleEq, codeEq, k8, entry1, save, noStack, noStore, noAlloc,
    maxOk⟩, good, ptr2, ptr3, ptr4, bp, r2, r3, r4, m0, m1, m2, m3, m4, cbEmpty, le, al2, al4,
    albp, big, heap⟩ := hyp
  apply makeInitOptWithArena_semantics generateGc maxHeap pointer start bitmaps dataSpace
    s2 arena jump bounds (sptFromAList code) oracle
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup]
  · have sub : -1 * ptr2 + ptr4 = ptr4 - ptr2 := by
      rw [BitVec.neg_mul]; simp [BitVec.sub_eq_add_neg, BitVec.add_comm]
    rw [sub] at heap
    exact ⟨ptr2, ptr3, ptr4, bp, good, k8, entry1, save, noStack, noStore, noAlloc, r2, r3, r4,
      m0, m1, m2, m3, m4, le, big, al2, al4, albp, cbEmpty, heap⟩
  · exact InitCodeRelation.impCodeRel jump bounds generateGc maxHeap pointer start code
      s2.code ⟨every, codeEq⟩
  · exact oracleEq
  · exact oracleBound
  · rw [codeEq, sptLookup_sptFromAList]
    simp [compileHOL, initStubs, sptAListLookup, stackErrLab]
  · exact maxOk

#print axioms makeInitSemanticsWithArena
end InitE.Op5
