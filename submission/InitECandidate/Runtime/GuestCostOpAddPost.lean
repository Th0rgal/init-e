import InitECandidate.Runtime.GuestFrameOpAddBridge
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- A stack word below the frame is never a funding cell. -/
private theorem below_ne_header (frame base : BitVec 64) (sp offset : BitVec 64)
    (below : (operandAddress base sp offset).toNat < frame.toNat)
    (extent : frame.toNat + 280 ≤ 2 ^ 64) (header : BitVec 64)
    (small : header.toNat < 280) (positive : 64 ≤ header.toNat) :
    operandAddress base sp offset ≠ frame + header := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  rw [BitVec.toNat_add_of_lt (by omega)] at natural
  omega

/-- The `charge_gas` continuation carries the charged funding. -/
theorem opAddGasState_funding (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3) :
    HasGasFunding (opAddGasState s frame sp x y funding) frame (funding.charge 3) := by
  have yFund : HasGasFunding (opAddYEntry s frame sp x y) frame funding := by
    refine ⟨?_, ?_, ?_⟩
    · rw [opAddYEntry_memory_ne s frame sp x y (frame + 64)]; exact inv.fundingMem.1
      exact GuestFrameInvariant.frameOffset_ne inv 64 16 (by decide) (by decide) (by decide)
    · rw [opAddYEntry_memory_ne s frame sp x y (frame + 184)]; exact inv.fundingMem.2.1
      exact GuestFrameInvariant.frameOffset_ne inv 184 16 (by decide) (by decide) (by decide)
    · rw [opAddYEntry_memory_ne s frame sp x y (frame + 192)]; exact inv.fundingMem.2.2
      exact GuestFrameInvariant.frameOffset_ne inv 192 16 (by decide) (by decide) (by decide)
  have entry : HasGasFunding
      (callEntryStateHOLFinite (opAddYEntry s frame sp x y) (chargeGasCallee 3)) frame funding := by
    simpa [HasGasFunding, callEntryStateHOLFinite] using yFund
  simpa [HasGasFunding, opAddGasState] using
    chargeGasPost_funding (callEntryStateHOLFinite (opAddYEntry s frame sp x y) (chargeGasCallee 3))
      frame 3 funding entry

/-- `u256_add` only rebinds locals, so the charged funding survives. -/
theorem opAddREntry_funding (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (memory : HasGasFunding (opAddGasState s frame sp x y funding) frame (funding.charge 3)) :
    HasGasFunding (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3) frame
      (funding.charge 3) := by
  have entry : HasGasFunding
      (callEntryStateHOLFinite (opAddGasState s frame sp x y funding)
        (u256AddCallee x y)) frame (funding.charge 3) := by
    simpa [HasGasFunding, callEntryStateHOLFinite] using memory
  simpa [HasGasFunding, opAddREntry, u256AddPost_memory, setVarHOLFinite] using entry

/-- The stack push writes only operand words and the pointer cell, all below the
frame, so the funding cells survive. -/
theorem opAddPushState_funding (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (memory : HasGasFunding (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3)
      frame (funding.charge 3)) :
    HasGasFunding (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3)
      frame (funding.charge 3) := by
  have entry : HasGasFunding
      (callEntryStateHOLFinite (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3)
        (stackPushCallee (opAddRValue a0 a1 a2 a3 b0 b1 b2 b3))) frame (funding.charge 3) := by
    simpa [HasGasFunding, callEntryStateHOLFinite] using memory
  change HasGasFunding
    (stackPushPost (callEntryStateHOLFinite (opAddREntry s frame sp x y funding
        a0 a1 a2 a3 b0 b1 b2 b3)
      (stackPushCallee (opAddRValue a0 a1 a2 a3 b0 b1 b2 b3)))
      frame (sp - 2) cap base (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1)
      (opAddLimb2 a0 a1 a2 b0 b1 b2) (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3))
      frame (funding.charge 3)
  have stackNe : ∀ (header offset : BitVec 64), header.toNat < 280 → 64 ≤ header.toNat →
      offset ∈ ([0, 8, 16, 24] : List (BitVec 64)) →
      frame + header ≠ base + (sp - 2) * 32 + offset := by
    intro header offset small positive mem
    have h := below_ne_header frame base (sp - 2) offset (inv.yBelow offset mem)
      inv.frameExtent header small positive
    simpa [operandAddress] using h.symm
  unfold HasGasFunding at entry ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [stackPushPost_memory_ne _ _ _ _ _ _ _ _ _ _
      (inv.frameOffset_ne 64 16 (by decide) (by decide) (by decide))
      (by simpa using stackNe 64 0 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 64 8 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 64 16 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 64 24 (by decide) (by decide) (by decide))]
    exact entry.1
  · rw [stackPushPost_memory_ne _ _ _ _ _ _ _ _ _ _
      (by simpa using inv.frameOffset_ne 184 16 (by decide) (by decide) (by decide))
      (by simpa using stackNe 184 0 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 184 8 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 184 16 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 184 24 (by decide) (by decide) (by decide))]
    exact entry.2.1
  · rw [stackPushPost_memory_ne _ _ _ _ _ _ _ _ _ _
      (by simpa using inv.frameOffset_ne 192 16 (by decide) (by decide) (by decide))
      (by simpa using stackNe 192 0 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 192 8 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 192 16 (by decide) (by decide) (by decide))
      (by simpa [panBytesInWord, BitVec.add_assoc] using stackNe 192 24 (by decide) (by decide) (by decide))]
    exact entry.2.2

/-- The `pc_add` continuation writes only `ev+0`, so the funding survives. -/
theorem opAddPcState_funding (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (memory : HasGasFunding
      (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3)
      frame (funding.charge 3)) :
    HasGasFunding (opAddPcState s frame sp cap base pc x y funding a0 a1 a2 a3 b0 b1 b2 b3)
      frame (funding.charge 3) := by
  have entry : HasGasFunding
      (callEntryStateHOLFinite
        (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3)
        (pcAddCallee 1)) frame (funding.charge 3) := by
    simpa [HasGasFunding, callEntryStateHOLFinite] using memory
  change HasGasFunding
    (emptyLocalsHOLFinite
      { callEntryStateHOLFinite
          (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3)
          (pcAddCallee 1) with
        memory := writeWordMemory
          (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3) (frame + 0) (pc + 1) })
    frame (funding.charge 3)
  simpa [HasGasFunding, emptyLocalsHOLFinite, callEntryStateHOLFinite, writeWordMemory,
    (inv.frameOffset_ne 64 0 (by decide) (by decide) (by decide)),
    (inv.frameOffset_ne 184 0 (by decide) (by decide) (by decide)),
    (inv.frameOffset_ne 192 0 (by decide) (by decide) (by decide))] using entry

/-- The full executed ADD post-state still carries exactly the three charged
gas units, and has advanced the pc cell. -/
theorem opAddFinalPost_funding (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3) :
    HasGasFunding
      (opAddFinalPost s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
        (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3)
      frame (funding.charge 3) := by
  have hZ := opAddGasState_funding s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
    (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3 inv
  have hR := opAddREntry_funding s frame sp (fourWordValue a0 a1 a2 a3)
    (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3 hZ
  have hP := opAddPushState_funding s frame sp cap base (fourWordValue a0 a1 a2 a3)
    (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3 inv hR
  have hPc := opAddPcState_funding s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
    (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3 inv hP
  simpa [HasGasFunding, opAddFinalPost, emptyLocalsHOLFinite] using hPc

/-- The ADD post advances the pc cell. -/
theorem opAddFinalPost_pc (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (opAddFinalPost s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 0) =
      .word (pc + 1) := by
  simp [opAddFinalPost, opAddPcState, emptyLocalsHOLFinite, writeWordMemory]

/-- The ADD post spends five source clocks: the six call entries of the arm
(two pops, charge_gas, u256_add, stack_push, pc_add). -/
theorem opAddFinalPost_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (opAddFinalPost s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock = s.clock - 6 := by
  have hy := opAddYEntry_clock s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3)
  change (opAddPcState s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
    (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock = s.clock - 6
  rw [show (opAddPcState s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
      (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock =
      (opAddPushState s frame sp cap base (fourWordValue a0 a1 a2 a3)
        (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock - 1 from rfl]
  rw [opAddPushState_clock, opAddREntry_clock, opAddGasState_clock, hy]
  omega

#print axioms opAddFinalPost_funding
#print axioms opAddFinalPost_pc
#print axioms opAddFinalPost_clock
end InitECandidate.Runtime.FineCost
