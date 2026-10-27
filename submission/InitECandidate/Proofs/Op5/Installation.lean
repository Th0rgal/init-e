import Flapjack.Compiler.Backend.Semantics.TargetSem.Installed

/-! Conservative installation contract extension: all pinned installation
clauses are retained. The only changes are the extra ordinary byte domain
and the corresponding bitmap exclusion. Stack disjointness is a separate
obligation on the source word domain (see MemoryDomain and Separation). -/
namespace InitE.Op5
open Flapjack

def installedWithArena {width : Nat} [NeZero width] {S Q : Type} (bytes : List (BitVec 8)) (cbspace : Nat)
    (bitmaps : List (BitVec width)) (dataSp : Nat) (ffiNames : Option (List HolFfiName))
    (regs : Nat × Nat) (mc : MachineConfig width S Q)
    (shmemExtra : List Compiler.Backend.LabToTarget.ShmemInfoNum) (ms : S)
    (arena : BitVec width → Bool) : Prop :=
  ∃ (t : AsmState width) (m : BitVec width → WordLocW width) (bitmapPtr : BitVec width)
    (bitmapsDm sdm : BitVec width → Bool),
    let bytesInWord := Compiler.Backend.StackRemove.bytesInWord width
    let heapStackDm : BitVec width → Bool :=
      fun w => decide (t.regs regs.1 ≤ w ∧ w < t.regs regs.2)
    goodInitState mc ms bytes cbspace t m (fun w => (heapStackDm w || arena w) || bitmapsDm w) sdm ∧
    holByteAligned (t.regs regs.1) = true ∧
    holByteAligned (t.regs regs.2) = true ∧
    holByteAligned bitmapPtr = true ∧
    t.regs regs.1 ≤ t.regs regs.2 ∧
    1024 * bytesInWord ≤ t.regs regs.2 - t.regs regs.1 ∧
    (∀ w, ¬ ((heapStackDm w = true ∨ arena w = true) ∧ bitmapsDm w = true)) ∧
    m (t.regs regs.1) = .word bitmapPtr ∧
    m (t.regs regs.1 + bytesInWord) =
      .word (bitmapPtr + bytesInWord * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs regs.1 + 2 * bytesInWord) =
      .word (bitmapPtr + bytesInWord * BitVec.ofNat width dataSp +
        bytesInWord * BitVec.ofNat width bitmaps.length) ∧
    m (t.regs regs.1 + 3 * bytesInWord) =
      .word (mc.target.getPc ms + BitVec.ofNat width bytes.length) ∧
    m (t.regs regs.1 + 4 * bytesInWord) =
      .word (mc.target.getPc ms + BitVec.ofNat width cbspace + BitVec.ofNat width bytes.length) ∧
    SetSep.star (Misc.wordList bitmapPtr (bitmaps.map WordLocW.word))
      (Misc.wordListExists (bitmapPtr + bytesInWord * BitVec.ofNat width bitmaps.length) dataSp)
      (SetSep.fun2Set (m, fun a => holByteAligned a = true ∧ bitmapsDm a = true)) ∧
    ffiNames = some mc.ffiNames ∧
    (∀ i, mmioPcsMinIndex mc.ffiNames = some i →
      shmemExtra.map (fun rec => (mc.target.getPc ms).toNat + rec.entryPc) =
          (mc.ffiEntryPcs.map BitVec.toNat).drop i ∧
        mc.mmioInfo = List.zip ((List.range shmemExtra.length).map (fun index => index + i))
          (shmemExtra.map fun rec => (rec.nbytes,
            Compiler.Encoders.Asm.HolAddr.addr rec.addrReg (BitVec.ofNat width rec.addrOff),
            rec.reg, BitVec.ofNat width rec.exitPc + mc.target.getPc ms)) ∧
        cbspace + bytes.length + Compiler.Backend.LabToTarget.ffiOffset * (i + 3) < 2 ^ width)


/-- The extended contract reduces to the pinned contract for an empty arena. -/
theorem installedWithArena_empty {width : Nat} [NeZero width] {S Q : Type}
    (bytes : List (BitVec 8)) (cbspace : Nat) (bitmaps : List (BitVec width))
    (dataSp : Nat) (ffiNames : Option (List HolFfiName)) (regs : Nat × Nat)
    (mc : MachineConfig width S Q)
    (extra : List Compiler.Backend.LabToTarget.ShmemInfoNum) (ms : S) :
    installedWithArena bytes cbspace bitmaps dataSp ffiNames regs mc extra ms (fun _ => false) ↔
      installed bytes cbspace bitmaps dataSp ffiNames regs mc extra ms := by
  simp only [installedWithArena, installed, Bool.or_false, Bool.false_eq_true,
    or_false]

#print axioms installedWithArena_empty
end InitE.Op5
