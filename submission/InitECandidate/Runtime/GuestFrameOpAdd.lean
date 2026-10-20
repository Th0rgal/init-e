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
#print axioms chargeGasPost_memory_ne
#print axioms stackPushPost_memory_ne
#print axioms opAddPcState_memory_ne
#print axioms opAddPcState_memory_pc
#print axioms opAddPcState_clock

end InitECandidate.Runtime.FineCost
