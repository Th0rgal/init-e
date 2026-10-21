import InitECandidate.Runtime.GuestCostOpAddBody
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- The concrete operand region of one `stack_pop`/`stack_push` slot. -/
def operandAddress (base : BitVec 64) (index : BitVec 64) (offset : BitVec 64) : BitVec 64 :=
  base + index * 32 + offset

/-- Offsets of the headers used by the EVM frame and the funding words. -/
def guestHeaderOffsets : List (BitVec 64) := [0, 8, 16, 64, 184, 232]

/-- A reusable actual guest frame invariant: the frame pointer, the concrete
operand stack header (base/index/capacity and program counter), the funding
cells, the two live operand slots, and the physical separation of the operand
buffer from the frame. It is exactly the state a compiled EVM opcode sees. -/
structure GuestFrameInvariant (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64) : Prop where
  ev : s.globals.lookup (ofString "ev") = some (.val (.word frame))
  code : s.code.lookup = originalRuntimeCode.lookup
  clock : 7 ≤ s.clock
  headerDomain : ∀ offset ∈ guestHeaderOffsets, s.memaddrs (frame + offset)
  baseCell : s.memory (frame + 8) = .word base
  spCell : s.memory (frame + 16) = .word sp
  capCell : s.memory (frame + 232) = .word cap
  pcCell : s.memory (frame + 0) = .word pc
  fundingMem : HasGasFunding s frame funding
  enough : (3 : BitVec 64) ≤ funding.left
  frameExtent : frame.toNat + 280 ≤ 2 ^ 64
  bufferExtent : base.toNat + cap.toNat * 32 ≤ frame.toNat
  capBound : cap.toNat ≤ 1024
  spLower : 2 ≤ sp.toNat
  spLeCap : sp.toNat ≤ cap.toNat
  xDomain0 : s.memaddrs (operandAddress base (sp - 1) 0)
  xDomain1 : s.memaddrs (operandAddress base (sp - 1) 8)
  xDomain2 : s.memaddrs (operandAddress base (sp - 1) 16)
  xDomain3 : s.memaddrs (operandAddress base (sp - 1) 24)
  xCell0 : s.memory (operandAddress base (sp - 1) 0) = .word a0
  xCell1 : s.memory (operandAddress base (sp - 1) 8) = .word a1
  xCell2 : s.memory (operandAddress base (sp - 1) 16) = .word a2
  xCell3 : s.memory (operandAddress base (sp - 1) 24) = .word a3
  yDomain0 : s.memaddrs (operandAddress base (sp - 2) 0)
  yDomain1 : s.memaddrs (operandAddress base (sp - 2) 8)
  yDomain2 : s.memaddrs (operandAddress base (sp - 2) 16)
  yDomain3 : s.memaddrs (operandAddress base (sp - 2) 24)
  yCell0 : s.memory (operandAddress base (sp - 2) 0) = .word b0
  yCell1 : s.memory (operandAddress base (sp - 2) 8) = .word b1
  yCell2 : s.memory (operandAddress base (sp - 2) 16) = .word b2
  yCell3 : s.memory (operandAddress base (sp - 2) 24) = .word b3
  xBelow : ∀ offset ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    (operandAddress base (sp - 1) offset).toNat < frame.toNat
  yBelow : ∀ offset ∈ ([0, 8, 16, 24] : List (BitVec 64)),
    (operandAddress base (sp - 2) offset).toNat < frame.toNat

namespace GuestFrameInvariant

/-- Entering a call preserves the whole frame invariant once the entry clock
is large enough: only locals and the clock change. -/
theorem callEntry_GuestFrameInvariant (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (clock : 7 ≤ (callEntryStateHOLFinite s callee).clock) :
    GuestFrameInvariant (callEntryStateHOLFinite s callee) frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  refine { inv with clock := clock }

/-- A frame offset stays in the frame record. -/
theorem frameOffset_toNat (inv : GuestFrameInvariant s frame sp cap base pc funding
    a0 a1 a2 a3 b0 b1 b2 b3) (offset : BitVec 64) (small : offset.toNat < 280) :
    (frame + offset).toNat = frame.toNat + offset.toNat :=
  BitVec.toNat_add_of_lt (by have := inv.frameExtent; omega)

/-- Distinct small frame offsets remain distinct addresses. -/
theorem frameOffset_ne (inv : GuestFrameInvariant s frame sp cap base pc funding
    a0 a1 a2 a3 b0 b1 b2 b3) (a b : BitVec 64) (aSmall : a.toNat < 280)
    (bSmall : b.toNat < 280) (different : a ≠ b) : frame + a ≠ frame + b := by
  intro equal
  have natural := congrArg BitVec.toNat equal
  rw [inv.frameOffset_toNat a aSmall, inv.frameOffset_toNat b bSmall] at natural
  exact different (BitVec.eq_of_toNat_eq (by omega))

/-- An operand word below the frame is never one of the frame's headers. -/
theorem operand_ne_header (inv : GuestFrameInvariant s frame sp cap base pc funding
    a0 a1 a2 a3 b0 b1 b2 b3) (address : BitVec 64) (offset : BitVec 64)
    (below : address.toNat < frame.toNat) (small : offset.toNat < 280) :
    address ≠ frame + offset := by
  intro equal
  have := congrArg BitVec.toNat equal
  rw [inv.frameOffset_toNat offset small] at this
  omega

end GuestFrameInvariant

/-- The pointer store of `stack_pop` leaves the address registry unchanged. -/
theorem stackPopStored_memaddrs {F : Type} (s : PanSemStateFiniteExact 64 F)
    (frame sp : BitVec 64) : (stackPopStored s frame sp).memaddrs = s.memaddrs := rfl

/-- The pointer store of `stack_pop` leaves the globals unchanged. -/
theorem stackPopStored_globals {F : Type} (s : PanSemStateFiniteExact 64 F)
    (frame sp : BitVec 64) : (stackPopStored s frame sp).globals = s.globals := rfl

/-- Any address other than the pointer cell is untouched by the `stack_pop` store. -/
theorem stackPopStored_memory_ne {F : Type} (s : PanSemStateFiniteExact 64 F)
    (frame sp address : BitVec 64) (different : address ≠ frame + 16) :
    (stackPopStored s frame sp).memory address = s.memory address := by
  unfold stackPopStored writeWordMemory
  simp only [stackPopAssigned, stackPopEntry, setVarHOLFinite, setKvarHOLFinite]
  rw [if_neg different]

/-- The pointer cell itself holds the decremented pointer. -/
theorem stackPopStored_memory_sp {F : Type} (s : PanSemStateFiniteExact 64 F)
    (frame sp : BitVec 64) :
    (stackPopStored s frame sp).memory (frame + 16) = .word (sp - 1) := by
  simp [stackPopStored, writeWordMemory]

/-- `has_gas_funding` survives the `stack_pop` pointer store. -/
theorem HasGasFunding.stackPopStored {F : Type} {s : PanSemStateFiniteExact 64 F}
    {frame sp : BitVec 64} {funding : GasFunding}
    (memory : HasGasFunding s frame funding)
    (leftNe : frame + 64 ≠ frame + 16) (usedNe : frame + 184 ≠ frame + 16)
    (spilledNe : frame + 192 ≠ frame + 16) :
    HasGasFunding (stackPopStored s frame sp) frame funding := by
  unfold HasGasFunding at *
  refine ⟨?_, ?_, ?_⟩
  · rw [stackPopStored_memory_ne _ _ _ _ leftNe]; exact memory.1
  · rw [stackPopStored_memory_ne _ _ _ _ usedNe]; exact memory.2.1
  · rw [stackPopStored_memory_ne _ _ _ _ spilledNe]; exact memory.2.2

/-- `has_gas_funding` is insensitive to local-variable updates. -/
theorem HasGasFunding.setVar {F : Type} {s : PanSemStateFiniteExact 64 F}
    {frame : BitVec 64} {funding : GasFunding} {name : MlStringHOL} {value : ValueHOL 64}
    (memory : HasGasFunding s frame funding) :
    HasGasFunding (setVarHOLFinite name value s) frame funding := by
  simpa [HasGasFunding, setVarHOLFinite] using memory

/-- `has_gas_funding` is insensitive to emptying the locals. -/
theorem HasGasFunding.emptyLocals {F : Type} {s : PanSemStateFiniteExact 64 F}
    {frame : BitVec 64} {funding : GasFunding}
    (memory : HasGasFunding s frame funding) :
    HasGasFunding (emptyLocalsHOLFinite s) frame funding := by
  simpa [HasGasFunding, emptyLocalsHOLFinite] using memory

#print axioms GuestFrameInvariant.frameOffset_ne
#print axioms stackPopStored_memory_ne
#print axioms HasGasFunding.stackPopStored
#print axioms HasGasFunding.setVar
#print axioms HasGasFunding.emptyLocals


/-- The first pop's continuation only writes the pointer cell. -/
theorem opAddXEntry_memory_ne (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x : ValueHOL 64) (address : BitVec 64)
    (different : address ≠ frame + 16) :
    (opAddXEntry s frame sp x).memory address = s.memory address := by
  simp only [opAddXEntry, stackPopSuccessPost, emptyLocalsHOLFinite, setVarHOLFinite,
    callEntryStateHOLFinite]
  rw [stackPopStored_memory_ne _ _ _ _ different]

/-- The two pops' continuation only writes the pointer cell. -/
theorem opAddYEntry_memory_ne (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) (address : BitVec 64)
    (different : address ≠ frame + 16) :
    (opAddYEntry s frame sp x y).memory address = s.memory address := by
  simp only [opAddYEntry, opAddXEntry, stackPopSuccessPost, emptyLocalsHOLFinite, setVarHOLFinite,
    callEntryStateHOLFinite]
  rw [stackPopStored_memory_ne _ _ _ _ different]
  rw [stackPopStored_memory_ne _ _ _ _ different]

/-- Clock after the first pop's continuation. -/
theorem opAddXEntry_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x : ValueHOL 64) :
    (opAddXEntry s frame sp x).clock = s.clock - 1 := by
  simp [opAddXEntry, stackPopSuccessPost, stackPopStored, stackPopAssigned, stackPopEntry,
    emptyLocalsHOLFinite, setVarHOLFinite, setKvarHOLFinite, callEntryStateHOLFinite]

/-- Clock after the second pop's continuation. -/
theorem opAddYEntry_clock (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (x y : ValueHOL 64) :
    (opAddYEntry s frame sp x y).clock = s.clock - 2 := by
  have hx := opAddXEntry_clock s frame sp x
  simp [opAddYEntry, hx, stackPopSuccessPost, stackPopStored, stackPopAssigned, stackPopEntry,
    emptyLocalsHOLFinite, setVarHOLFinite, setKvarHOLFinite, callEntryStateHOLFinite]
  omega


/-- A pointer store never touches an operand word below the frame. -/
theorem stackPopStored_memory_below {F : Type} (s : PanSemStateFiniteExact 64 F)
    (frame sp address : BitVec 64) (below : address.toNat < frame.toNat)
    (extent : frame.toNat + 280 ≤ 2 ^ 64) :
    (stackPopStored s frame sp).memory address = s.memory address := by
  apply stackPopStored_memory_ne
  intro equal
  rw [equal] at below
  have hframe : frame.toNat + 16 < 2 ^ 64 := by omega
  have natural : (frame + 16).toNat = frame.toNat + 16 :=
    BitVec.toNat_add_of_lt hframe
  omega

#print axioms stackPopStored_memory_below
#print axioms opAddXEntry_memory_ne
#print axioms opAddYEntry_memory_ne
#print axioms opAddXEntry_clock
#print axioms opAddYEntry_clock
/-- Updating locals never changes the frame invariant. -/
theorem setVar_GuestFrameInvariant (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (name : MlS) (value : ValueHOL 64)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3) :
    GuestFrameInvariant (setVarHOLFinite name value s) frame sp cap base pc funding
      a0 a1 a2 a3 b0 b1 b2 b3 := by
  cases inv with
  | mk ev code clock hd b sc cc pcv fm en fe be cb sl scp xd0 xd1 xd2 xd3 xc0 xc1 xc2 xc3
      yd0 yd1 yd2 yd3 yc0 yc1 yc2 yc3 xb yb =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals simp_all [setVarHOLFinite, HasGasFunding]

#print axioms setVar_GuestFrameInvariant

end InitECandidate.Runtime.FineCost
