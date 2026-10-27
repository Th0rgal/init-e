import InitECandidate.Proofs.Op5.LabInitArena
import Flapjack.Pancake.Proofs.PanToTarget.AssemblyMemory

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Pancake.Proofs.PanToTarget
open Classical

theorem memoryAssumptionFromMachineWithArena {width : Nat} [NeZero width] {S Q F C : Type}
    (good : goodDimindex width) (regNames : Spt Nat) (mc : MachineConfig width S Q)
    (ffi : HolFfiState F) (t : AsmState width) (m : BitVec width → WordLocW width)
    (bitmapPtr : BitVec width) (bitmapsDm sdm' : BitVec width → Bool) (ms : S)
    (code : LabSem.LabProgHOL width)
    (comp : C → LabSem.LabProgHOL width → Option (List (BitVec 8) × C))
    (bytes : List (BitVec 8)) (cbspace : Nat) (coracle : Nat → C × LabSem.LabProgHOL width)
    (bitmaps : List (BitVec width)) (dataSp : Nat) (byteArena : BitVec width → Bool) (arena : BitVec width → Prop)
    (wordArenaEq : ∀ a, arena a ↔ byteArena a = true ∧ holByteAligned a = true)
    (arenaHeap : ∀ a, arena a → ¬(t.regs (StackNames.findNameSpt regNames 2) ≤ a ∧
      a < t.regs (StackNames.findNameSpt regNames 4)))
    (arenaBitmap : ∀ a, arena a → bitmapsDm a ≠ true) :
    let r1 := StackNames.findNameSpt regNames 2
    let r2 := StackNames.findNameSpt regNames 4
    let biw := StackRemove.bytesInWord width
    let heapStackDm : BitVec width → Bool := fun w => decide (t.regs r1 ≤ w ∧ w < t.regs r2)
    holByteAligned (t.regs r1) = true ∧ holByteAligned (t.regs r2) = true ∧
    holByteAligned bitmapPtr = true ∧ t.regs r1 ≤ t.regs r2 ∧
    1024 * biw ≤ t.regs r2 - t.regs r1 ∧
    (∀ w, ¬ (heapStackDm w = true ∧ bitmapsDm w = true)) ∧
    m (t.regs r1) = .word bitmapPtr ∧
    m (t.regs r1 + biw) = .word (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs r1 + 2 * biw) = .word (bitmapPtr + biw * BitVec.ofNat width dataSp +
      biw * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs r1 + 3 * biw) = .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
    m (t.regs r1 + 4 * biw) =
      .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
    SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
      (Misc.wordListExists (bitmapPtr + biw * BitVec.ofNat width bitmaps.length) dataSp)
      (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)) →
    memoryAssumptionWithArena regNames bitmaps dataSp
      (LabToTarget.makeInit (C := C) mc ffi t m
        (fun a => ((heapStackDm a || byteArena a) || bitmapsDm a) && holByteAligned a) sdm' ms code comp
        (mc.target.getPc ms + BitVec.ofNat width bytes.length) cbspace coracle) arena := by
  intro r1 r2 biw heapStackDm
  rintro ⟨ha1, ha2, hbp, hle, hsize, hdisj, hm0, hm1, hm2, hm3, hm4, hstar⟩
  have hdw : (-1 * t.regs r1 + t.regs r2).toNat / (width / 8) * (width / 8) < 2 ^ width :=
    Nat.lt_of_le_of_lt (Nat.div_mul_le_self _ _) (BitVec.isLt _)
  refine ⟨t.regs r1, t.regs (StackNames.findNameSpt regNames 3), t.regs r2, bitmapPtr,
    rfl, rfl, rfl, hm0, hm1, hm2, hm3, ?_, rfl, hle, ha1, ha2, hbp, hsize, ?_⟩
  · simp only [LabToTarget.makeInit]
    rw [hm4]
    congr 1
    ac_rfl
  · simp only [LabToTarget.makeInit, bytesInWord_toNat good]
    have hset : (fun a => (((heapStackDm a || byteArena a) || bitmapsDm a) &&
        holByteAligned a) = true) =
        (fun a => ((holByteAligned a = true ∧ bitmapsDm a = true) ∨ arena a) ∨
          (holByteAligned a = true ∧ t.regs r1 ≤ a ∧ a < t.regs r2)) := by
      funext a
      apply propext
      simp only [heapStackDm, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
      have := wordArenaEq a
      tauto
    rw [hset]
    apply Misc.Fun2SetUnion.fun2SetDisjointUnion
    refine ⟨?_, ?_, ?_⟩
    · intro a ⟨hb, _, hh⟩
      rcases hb with ⟨_, hb⟩ | ha
      · exact hdisj a ⟨by simp [heapStackDm, hh], hb⟩
      · exact arenaHeap a ha hh
    · apply Misc.Fun2SetUnion.fun2SetDisjointUnion
      refine ⟨?_, hstar, ?_⟩
      · intro a ⟨⟨_, hb⟩, ha⟩
        exact arenaBitmap a ha hb
      · rfl
    · rw [alignedInterval_eq_addresses good _ _ ha1 ha2 hle]
      exact BackendProof.wordListExistsImp _ _ _ _ ⟨rfl, by rw [Nat.mul_comm]; exact hdw, good⟩

#print axioms memoryAssumptionFromMachineWithArena
end InitE.Op5
