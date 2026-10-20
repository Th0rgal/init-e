import InitECandidate.Runtime.GuestFrameInvariant
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- `charge_gas` writes only `ev+64` and `ev+184`. -/
theorem chargeGasPost_memory_ne (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used amount address : BitVec 64)
    (leftNe : address ≠ frame + 64) (usedNe : address ≠ frame + 184) :
    (chargeGasPost s frame left used amount).memory address = s.memory address := by
  unfold chargeGasPost sourceWriteWord
  simp only [emptyLocalsHOLFinite, setVarHOLFinite]
  rw [if_neg usedNe, if_neg leftNe]

/-- `charge_gas` never changes the clock. -/
theorem chargeGasPost_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame left used amount : BitVec 64) :
    (chargeGasPost s frame left used amount).clock = s.clock := rfl

/-- The four-limb `u256_add` post only rebinds locals. -/
theorem u256AddPost_memory (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (u256AddPost s a0 a1 a2 a3 b0 b1 b2 b3).memory = s.memory := rfl

/-- The four-limb `u256_add` post never changes the clock. -/
theorem u256AddPost_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (u256AddPost s a0 a1 a2 a3 b0 b1 b2 b3).clock = s.clock := rfl

/-- A word store at a different address leaves a cell untouched. -/
theorem writeWordMem_other (memory : RiscV.Word 64 → HolWordLab 64) (written value address : BitVec 64)
    (different : address ≠ written) :
    writeWordMem memory written value address = memory address := by
  simp [writeWordMem, different]

/-- The successful `stack_push` post writes the four operand words and `ev+16`. -/
theorem stackPushPost_memory_ne (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base v0 v1 v2 v3 address : BitVec 64)
    (h16 : address ≠ frame + 16)
    (h0 : address ≠ base + sp * 32)
    (h1 : address ≠ base + sp * 32 + panBytesInWord 64)
    (h2 : address ≠ base + sp * 32 + panBytesInWord 64 + panBytesInWord 64)
    (h3 : address ≠ base + sp * 32 + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64) :
    (stackPushPost s frame sp cap base v0 v1 v2 v3).memory address = s.memory address := by
  unfold stackPushPost stackPushCapEntry stackPopEntry writeWordMemory writeWord4Memory
  simp only [setVarHOLFinite, setKvarHOLFinite, emptyLocalsHOLFinite] at *
  rw [if_neg (show address ≠ frame + 16 from h16)]
  rw [writeWordMem_other _ _ _ _ h3]
  rw [writeWordMem_other _ _ _ _ h2]
  rw [writeWordMem_other _ _ _ _ h1]
  rw [writeWordMem_other _ _ _ _ h0]

/-- The successful `stack_push` post never changes the clock. -/
theorem stackPushPost_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base v0 v1 v2 v3 : BitVec 64) :
    (stackPushPost s frame sp cap base v0 v1 v2 v3).clock = s.clock := rfl

/-- The `pc_add` continuation writes only `ev+0`. -/
theorem opAddPcState_memory_ne (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) (address : BitVec 64)
    (different : address ≠ frame) :
    (opAddPcState s frame sp cap base pc x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory address =
      (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory address := by
  simp [opAddPcState, writeWordMemory, emptyLocalsHOLFinite, setVarHOLFinite,
    callEntryStateHOLFinite, different]

/-- The `pc_add` continuation writes the incremented program counter. -/
theorem opAddPcState_memory_pc (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (opAddPcState s frame sp cap base pc x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory
        (frame + 0) = .word (pc + 1) := by
  simp [opAddPcState, writeWordMemory, emptyLocalsHOLFinite, setVarHOLFinite,
    callEntryStateHOLFinite]

/-- The `pc_add` continuation decrements the clock once. -/
theorem opAddPcState_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (opAddPcState s frame sp cap base pc x y funding a0 a1 a2 a3 b0 b1 b2 b3).clock =
      (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3).clock - 1 := by
  simp [opAddPcState, emptyLocalsHOLFinite, setVarHOLFinite, callEntryStateHOLFinite]


/-- The two pops leave the funding cells and the gas budget intact. -/
theorem opAddYEntry_funding (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (memory : HasGasFunding s frame funding)
    (leftNe : frame + 64 ≠ frame + 16) (usedNe : frame + 184 ≠ frame + 16)
    (spilledNe : frame + 192 ≠ frame + 16) :
    HasGasFunding (opAddYEntry s frame sp x y) frame funding := by
  unfold HasGasFunding at *
  refine ⟨?_, ?_, ?_⟩
  · rw [opAddYEntry_memory_ne s frame sp x y (frame + 64) leftNe]; exact memory.1
  · rw [opAddYEntry_memory_ne s frame sp x y (frame + 184) usedNe]; exact memory.2.1
  · rw [opAddYEntry_memory_ne s frame sp x y (frame + 192) spilledNe]; exact memory.2.2

#print axioms opAddYEntry_funding

/-- The first stacked pointer after the first pop. -/
theorem opAddXEntry_memory_sp (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x : ValueHOL 64) :
    (opAddXEntry s frame sp x).memory (frame + 16) = .word (sp - 1) := by
  simpa [opAddXEntry, stackPopSuccessPost, emptyLocalsHOLFinite, setVarHOLFinite,
    callEntryStateHOLFinite] using
    stackPopStored_memory_sp (callEntryStateHOLFinite s HolFiniteMapExact.empty) frame sp

/-- The second stacked pointer after both pops. -/
theorem opAddYEntry_memory_sp (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) :
    (opAddYEntry s frame sp x y).memory (frame + 16) = .word (sp - 2) := by
  have hsub : sp - 1 - 1 = sp - 2 := by bv_omega
  have h := stackPopStored_memory_sp
    (callEntryStateHOLFinite (opAddXEntry s frame sp x) HolFiniteMapExact.empty) frame (sp - 1)
  rw [hsub] at h
  simpa [opAddYEntry, stackPopSuccessPost, emptyLocalsHOLFinite, setVarHOLFinite,
    callEntryStateHOLFinite] using h

/-- Gas and the four-limb add leave the stacked pointer at `sp-2`. -/
theorem opAddREntry_memory_sp (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (leftNe : frame + 16 ≠ frame + 64) (usedNe : frame + 16 ≠ frame + 184) :
    (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 16) =
      .word (sp - 2) := by
  have hy := opAddYEntry_memory_sp s frame sp x y
  simpa [opAddREntry, opAddGasState, u256AddPost, chargeGasPost, sourceWriteWord,
    emptyLocalsHOLFinite, setVarHOLFinite, callEntryStateHOLFinite, leftNe, usedNe] using hy

/-- Gas and the four-limb add leave the operand base cell intact. -/
theorem opAddREntry_memory_base (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (base : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (baseNe16 : frame + 8 ≠ frame + 16)
    (baseNe : frame + 8 ≠ frame + 64) (baseUsed : frame + 8 ≠ frame + 184)
    (cell : s.memory (frame + 8) = .word base) :
    (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 8) =
      .word base := by
  have hy := opAddYEntry_memory_ne s frame sp x y (frame + 8) baseNe16
  simpa [opAddREntry, opAddGasState, u256AddPost, chargeGasPost, sourceWriteWord,
    emptyLocalsHOLFinite, setVarHOLFinite, callEntryStateHOLFinite, baseNe, baseUsed]
    using hy.trans cell

/-- Gas and the four-limb add leave the capacity cell intact. -/
theorem opAddREntry_memory_cap (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (cap : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (capNe16 : frame + 232 ≠ frame + 16)
    (capNe : frame + 232 ≠ frame + 64) (capUsed : frame + 232 ≠ frame + 184)
    (cell : s.memory (frame + 232) = .word cap) :
    (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 232) =
      .word cap := by
  have hy := opAddYEntry_memory_ne s frame sp x y (frame + 232) capNe16
  simpa [opAddREntry, opAddGasState, u256AddPost, chargeGasPost, sourceWriteWord,
    emptyLocalsHOLFinite, setVarHOLFinite, callEntryStateHOLFinite, capNe, capUsed]
    using hy.trans cell

#print axioms opAddXEntry_memory_sp
#print axioms opAddYEntry_memory_sp
#print axioms opAddREntry_memory_sp
#print axioms opAddREntry_memory_base
#print axioms opAddREntry_memory_cap

/-- Gas and the four-limb add leave the program counter cell intact. -/
theorem opAddREntry_memory_frame (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (frameNe16 : frame ≠ frame + 16) (frameNe64 : frame ≠ frame + 64)
    (frameNe184 : frame ≠ frame + 184)
    (cell : s.memory frame = .word pc) :
    (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory frame =
      .word pc := by
  have hy := opAddYEntry_memory_ne s frame sp x y frame frameNe16
  simpa [opAddREntry, opAddGasState, u256AddPost, chargeGasPost, sourceWriteWord,
    emptyLocalsHOLFinite, setVarHOLFinite, callEntryStateHOLFinite, frameNe64, frameNe184]
    using hy.trans cell

/-- The `stack_push` continuation leaves the program counter cell intact. -/
theorem opAddPushState_memory_pc (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (h16 : frame ≠ frame + 16)
    (h0 : frame ≠ base + (sp - 2) * 32)
    (h1 : frame ≠ base + (sp - 2) * 32 + panBytesInWord 64)
    (h2 : frame ≠ base + (sp - 2) * 32 + panBytesInWord 64 + panBytesInWord 64)
    (h3 : frame ≠ base + (sp - 2) * 32 + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64)
    (cell : (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory frame =
      .word pc) :
    (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3).memory frame =
      .word pc := by
  have hp := stackPushPost_memory_ne
    (callEntryStateHOLFinite (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3)
      (stackPushCallee (opAddRValue a0 a1 a2 a3 b0 b1 b2 b3)))
    frame (sp - 2) cap base
    (opAddLimb0 a0 b0) (opAddLimb1 a0 a1 b0 b1) (opAddLimb2 a0 a1 a2 b0 b1 b2)
    (opAddLimb3 a0 a1 a2 a3 b0 b1 b2 b3) frame h16 h0 h1 h2 h3
  simpa [opAddPushState, callEntryStateHOLFinite] using hp.trans cell

#print axioms opAddREntry_memory_frame
#print axioms opAddPushState_memory_pc
#print axioms chargeGasPost_memory_ne
#print axioms stackPushPost_memory_ne
#print axioms opAddPcState_memory_ne
#print axioms opAddPcState_memory_pc
#print axioms opAddPcState_clock


/-- The first pop's continuation leaves the address registry unchanged. -/
theorem opAddXEntry_memaddrs (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x : ValueHOL 64) :
    (opAddXEntry s frame sp x).memaddrs = s.memaddrs := rfl

/-- The two pops' continuation leaves the address registry unchanged. -/
theorem opAddYEntry_memaddrs (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) :
    (opAddYEntry s frame sp x y).memaddrs = s.memaddrs := rfl

/-- Gas and the four-limb add leave the address registry unchanged. -/
theorem opAddREntry_memaddrs (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs = s.memaddrs := rfl


/-- One call clock step from the two-pop continuation to the gas call. -/
theorem opAddGasState_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding) :
    (opAddGasState s frame sp x y funding).clock = (opAddYEntry s frame sp x y).clock - 1 := rfl

/-- One call clock step from the gas call to the four-limb add. -/
theorem opAddREntry_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).clock =
      (opAddGasState s frame sp x y funding).clock - 1 := rfl

/-- One call clock step from the four-limb add to the push. -/
theorem opAddPushState_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base : BitVec 64) (x y : ValueHOL 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) :
    (opAddPushState s frame sp cap base x y funding a0 a1 a2 a3 b0 b1 b2 b3).clock =
      (opAddREntry s frame sp x y funding a0 a1 a2 a3 b0 b1 b2 b3).clock - 1 := rfl

#print axioms opAddGasState_clock
#print axioms opAddREntry_clock
#print axioms opAddPushState_clock


/-- A stack pointer at least two words deep does not decrement to zero. -/
theorem sp_sub_one_ne_zero (sp : BitVec 64) (lower : 2 ≤ sp.toNat) : sp - 1 ≠ 0 := by
  intro zero
  have oneNat : (1 : BitVec 64).toNat = 1 := by decide
  have le : (1 : BitVec 64) ≤ sp := by
    show (1 : BitVec 64).toNat ≤ sp.toNat
    rw [oneNat]
    omega
  have natural := BitVec.toNat_sub_of_le (x := sp) (y := 1) le
  have zeroNat : (sp - 1).toNat = 0 := by rw [zero]; rfl
  rw [natural, oneNat] at zeroNat
  omega

#print axioms sp_sub_one_ne_zero


/-- The two-deep stack pointer stays strictly below the capacity. -/
theorem sp_sub_two_below_cap (sp cap : BitVec 64) (lower : 2 ≤ sp.toNat)
    (le : sp.toNat ≤ cap.toNat) : (sp - 2).toNat < cap.toNat := by
  have twoNat : (2 : BitVec 64).toNat = 2 := by decide
  have le2 : (2 : BitVec 64) ≤ sp := by
    show (2 : BitVec 64).toNat ≤ sp.toNat
    rw [twoNat]
    omega
  have natural := BitVec.toNat_sub_of_le (x := sp) (y := 2) le2
  rw [natural, twoNat]
  omega

/-- A pointer below the capacity is never the full-stack sentinel. -/
theorem sp_sub_two_ne_1024 (sp cap : BitVec 64)
    (below : (sp - 2).toNat < cap.toNat) (bound : cap.toNat ≤ 1024) :
    sp - 2 ≠ (1024 : BitVec 64) := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  have sentinel : (1024 : BitVec 64).toNat = 1024 := by decide
  rw [sentinel] at natural
  omega

#print axioms sp_sub_two_below_cap
#print axioms sp_sub_two_ne_1024


/-- Entering a call changes no memory cell address. -/
theorem callEntryStateHOLFinite_memaddrs (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    (callEntryStateHOLFinite s callee).memaddrs = s.memaddrs := rfl

#print axioms callEntryStateHOLFinite_memaddrs

end InitECandidate.Runtime.FineCost
