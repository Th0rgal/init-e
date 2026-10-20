import InitECandidate.Runtime.GuestFrameOpAdd
namespace InitECandidate.Runtime.FineCost
open InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000

/-- The reusable actual guest frame invariant discharges every physical premise
of the exact ADD body trace. -/
theorem opAdd_body_run_of_frame
    (coeff : Work) (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3) :
    StatementRun s (sourceFunctionBody Guest.guestFn_op_add)
      (some (.returned (.val (.word 0))))
      (opAddFinalPost s frame sp cap base pc (fourWordValue a0 a1 a2 a3)
        (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3)
      (opAddEvents s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3) := by
  classical
  let xv : ValueHOL 64 := fourWordValue a0 a1 a2 a3
  let yv : ValueHOL 64 := fourWordValue b0 b1 b2 b3
  have hsub : sp - 1 - 1 = sp - 2 := by bv_omega
  have h8 : frame + 8 ≠ frame + 16 :=
    inv.frameOffset_ne 8 16 (by decide) (by decide) (by decide)
  have h64 : frame + 64 ≠ frame + 16 :=
    inv.frameOffset_ne 64 16 (by decide) (by decide) (by decide)
  have h184 : frame + 184 ≠ frame + 16 :=
    inv.frameOffset_ne 184 16 (by decide) (by decide) (by decide)
  have h192 : frame + 192 ≠ frame + 16 :=
    inv.frameOffset_ne 192 16 (by decide) (by decide) (by decide)
  have hx0 : (base + (sp - 1) * 32).toNat < frame.toNat := by
    simpa [operandAddress] using inv.xBelow 0 (by simp)
  have hx1 : (base + (sp - 1) * 32 + 8).toNat < frame.toNat := by
    simpa [operandAddress] using inv.xBelow 8 (by simp)
  have hx2 : (base + (sp - 1) * 32 + 16).toNat < frame.toNat := by
    simpa [operandAddress] using inv.xBelow 16 (by simp)
  have hx3 : (base + (sp - 1) * 32 + 24).toNat < frame.toNat := by
    simpa [operandAddress] using inv.xBelow 24 (by simp)
  have hy0 : (base + (sp - 2) * 32).toNat < frame.toNat := by
    simpa [operandAddress] using inv.yBelow 0 (by simp)
  have hy1 : (base + (sp - 2) * 32 + 8).toNat < frame.toNat := by
    simpa [operandAddress] using inv.yBelow 8 (by simp)
  have hy2 : (base + (sp - 2) * 32 + 16).toNat < frame.toNat := by
    simpa [operandAddress] using inv.yBelow 16 (by simp)
  have hy3 : (base + (sp - 2) * 32 + 24).toNat < frame.toNat := by
    simpa [operandAddress] using inv.yBelow 24 (by simp)
  have hxne0 : base + (sp - 1) * 32 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hx0 (by decide)
  have hxne1 : base + (sp - 1) * 32 + 8 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hx1 (by decide)
  have hxne2 : base + (sp - 1) * 32 + 16 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hx2 (by decide)
  have hxne3 : base + (sp - 1) * 32 + 24 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hx3 (by decide)
  have hyne0 : base + (sp - 2) * 32 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hy0 (by decide)
  have hyne1 : base + (sp - 2) * 32 + 8 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hy1 (by decide)
  have hyne2 : base + (sp - 2) * 32 + 16 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hy2 (by decide)
  have hyne3 : base + (sp - 2) * 32 + 24 ≠ frame + 16 :=
    inv.operand_ne_header _ 16 hy3 (by decide)
  have hframe16 : frame ≠ frame + 16 := by simpa using inv.frameOffset_ne 0 16 (by decide) (by decide) (by decide)
  have hframe64 : frame ≠ frame + 64 := by simpa using inv.frameOffset_ne 0 64 (by decide) (by decide) (by decide)
  have hframe184 : frame ≠ frame + 184 := by simpa using inv.frameOffset_ne 0 184 (by decide) (by decide) (by decide)
  have hs0 : frame ≠ base + (sp - 2) * 32 := by
    have h := inv.operand_ne_header (operandAddress base (sp - 2) 0) 0 (inv.yBelow 0 (by simp)) (by decide)
    simpa [operandAddress] using Ne.symm h
  have hs1 : frame ≠ base + (sp - 2) * 32 + panBytesInWord 64 := by
    have h := inv.operand_ne_header (operandAddress base (sp - 2) 8) 0 (inv.yBelow 8 (by simp)) (by decide)
    simpa [operandAddress, panBytesInWord] using Ne.symm h
  have hs2 : frame ≠ base + (sp - 2) * 32 + panBytesInWord 64 + panBytesInWord 64 := by
    have h := inv.operand_ne_header (operandAddress base (sp - 2) 16) 0 (inv.yBelow 16 (by simp)) (by decide)
    simpa [operandAddress, panBytesInWord, BitVec.add_assoc] using Ne.symm h
  have hs3 : frame ≠ base + (sp - 2) * 32 + panBytesInWord 64 + panBytesInWord 64 + panBytesInWord 64 := by
    have h := inv.operand_ne_header (operandAddress base (sp - 2) 24) 0 (inv.yBelow 24 (by simp)) (by decide)
    simpa [operandAddress, panBytesInWord, BitVec.add_assoc] using Ne.symm h
  have h_installed : s.code.lookup = originalRuntimeCode.lookup := inv.code
  have h_hFrame : s.globals.lookup (ofString "ev") = some (.val (.word frame)) := inv.ev
  have h_clock0 : s.clock ≠ 0 := by have := inv.clock; omega
  have h_spDomain : s.memaddrs (frame + 16) := inv.headerDomain 16 (by simp [guestHeaderOffsets])
  have h_spCell : s.memory (frame + 16) = .word sp := inv.spCell
  have h_nonzero : sp ≠ 0 := by have := inv.spLower; bv_omega
  have h_baseDomain : s.memaddrs (frame + 8) := inv.headerDomain 8 (by simp [guestHeaderOffsets])
  have h_baseCell : s.memory (frame + 8) = .word base := inv.baseCell
  have h_xDomain0 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32) := by rw [stackPopStored_memaddrs]; simpa [operandAddress] using inv.xDomain0
  have h_xDomain1 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32 + 8) := by rw [stackPopStored_memaddrs]; simpa [operandAddress] using inv.xDomain1
  have h_xDomain2 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32 + 16) := by rw [stackPopStored_memaddrs]; simpa [operandAddress] using inv.xDomain2
  have h_xDomain3 : (stackPopStored s frame sp).memaddrs (base + (sp - 1) * 32 + 24) := by rw [stackPopStored_memaddrs]; simpa [operandAddress] using inv.xDomain3
  have h_xCell0 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32) = .word a0 := by rw [stackPopStored_memory_below _ _ _ _ hx0 inv.frameExtent]; simpa [operandAddress] using inv.xCell0
  have h_xCell1 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32 + 8) = .word a1 := by rw [stackPopStored_memory_below _ _ _ _ hx1 inv.frameExtent]; simpa [operandAddress] using inv.xCell1
  have h_xCell2 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32 + 16) = .word a2 := by rw [stackPopStored_memory_below _ _ _ _ hx2 inv.frameExtent]; simpa [operandAddress] using inv.xCell2
  have h_xCell3 : (stackPopStored s frame sp).memory (base + (sp - 1) * 32 + 24) = .word a3 := by rw [stackPopStored_memory_below _ _ _ _ hx3 inv.frameExtent]; simpa [operandAddress] using inv.xCell3
  have h_clockX : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).clock ≠ 0 := by have := inv.clock; rw [opAddXEntry_clock]; omega
  have h_nonzeroY : (sp - 1) ≠ 0 := sp_sub_one_ne_zero sp inv.spLower
  have h_spYDomain : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memaddrs (frame + 16) := by rw [opAddXEntry_memaddrs]; exact inv.headerDomain 16 (by simp [guestHeaderOffsets])
  have h_spYCell : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memory (frame + 16) = .word (sp - 1) := opAddXEntry_memory_sp s frame sp xv
  have h_baseYDomain : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memaddrs (frame + 8) := by rw [opAddXEntry_memaddrs]; exact inv.headerDomain 8 (by simp [guestHeaderOffsets])
  have h_baseYCell : (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)).memory (frame + 8) = .word base := by rw [opAddXEntry_memory_ne s frame sp xv (frame + 8) h8]; exact inv.baseCell
  have h_yDomain0 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32) := by rw [hsub, stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs, opAddXEntry_memaddrs]; simpa [operandAddress] using inv.yDomain0
  have h_yDomain1 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32 + 8) := by rw [hsub, stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs, opAddXEntry_memaddrs]; simpa [operandAddress] using inv.yDomain1
  have h_yDomain2 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32 + 16) := by rw [hsub, stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs, opAddXEntry_memaddrs]; simpa [operandAddress] using inv.yDomain2
  have h_yDomain3 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memaddrs (base + (sp - 1 - 1) * 32 + 24) := by rw [hsub, stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs, opAddXEntry_memaddrs]; simpa [operandAddress] using inv.yDomain3
  have h_yCell0 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memory (base + (sp - 1 - 1) * 32) = .word b0 := by
      rw [hsub]
      rw [stackPopStored_memory_below _ _ _ _ hy0 inv.frameExtent]
      change (opAddXEntry s frame sp xv).memory (base + (sp - 2) * 32) = .word b0
      rw [opAddXEntry_memory_ne s frame sp xv _ hyne0]
      simpa [operandAddress] using inv.yCell0
  have h_yCell1 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memory (base + (sp - 1 - 1) * 32 + 8) = .word b1 := by
      rw [hsub]
      rw [stackPopStored_memory_below _ _ _ _ hy1 inv.frameExtent]
      change (opAddXEntry s frame sp xv).memory (base + (sp - 2) * 32 + 8) = .word b1
      rw [opAddXEntry_memory_ne s frame sp xv _ hyne1]
      simpa [operandAddress] using inv.yCell1
  have h_yCell2 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memory (base + (sp - 1 - 1) * 32 + 16) = .word b2 := by
      rw [hsub]
      rw [stackPopStored_memory_below _ _ _ _ hy2 inv.frameExtent]
      change (opAddXEntry s frame sp xv).memory (base + (sp - 2) * 32 + 16) = .word b2
      rw [opAddXEntry_memory_ne s frame sp xv _ hyne2]
      simpa [operandAddress] using inv.yCell2
  have h_yCell3 : (stackPopStored (callEntryStateHOLFinite (opAddXEntry s frame sp (fourWordValue a0 a1 a2 a3)) HolFiniteMapExact.empty) frame (sp - 1)).memory (base + (sp - 1 - 1) * 32 + 24) = .word b3 := by
      rw [hsub]
      rw [stackPopStored_memory_below _ _ _ _ hy3 inv.frameExtent]
      change (opAddXEntry s frame sp xv).memory (base + (sp - 2) * 32 + 24) = .word b3
      rw [opAddXEntry_memory_ne s frame sp xv _ hyne3]
      simpa [operandAddress] using inv.yCell3
  have h_clockY : (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3)).clock ≠ 0 := by have := inv.clock; rw [opAddYEntry_clock]; omega
  have h_fundingY : HasGasFunding (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3)) frame funding := opAddYEntry_funding s frame sp xv yv funding inv.fundingMem h64 h184 h192
  have h_enough : (3 : BitVec 64) ≤ funding.left := inv.enough
  have h_gasLeftDomain : (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3)).memaddrs (frame + 64) := by rw [opAddYEntry_memaddrs]; exact inv.headerDomain 64 (by simp [guestHeaderOffsets])
  have h_gasUsedDomain : (opAddYEntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3)).memaddrs (frame + 184) := by rw [opAddYEntry_memaddrs]; exact inv.headerDomain 184 (by simp [guestHeaderOffsets])
  have h_clockZ : (opAddGasState s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding).clock ≠ 0 := by have := inv.clock; rw [opAddGasState_clock, opAddYEntry_clock]; omega
  have h_clockR : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock ≠ 0 := by have := inv.clock; rw [opAddREntry_clock, opAddGasState_clock, opAddYEntry_clock]; omega
  have h_pushSpDomain : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 16) := by rw [opAddREntry_memaddrs]; exact inv.headerDomain 16 (by simp [guestHeaderOffsets])
  have h_pushSpCell : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 16) = .word (sp - 2) := opAddREntry_memory_sp s frame sp xv yv funding a0 a1 a2 a3 b0 b1 b2 b3 (Ne.symm h64) (Ne.symm h184)
  have h_capDomain : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 232) := by rw [opAddREntry_memaddrs]; exact inv.headerDomain 232 (by simp [guestHeaderOffsets])
  have h_capCell : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 232) = .word cap := opAddREntry_memory_cap s frame sp cap xv yv funding a0 a1 a2 a3 b0 b1 b2 b3 (inv.frameOffset_ne 232 16 (by decide) (by decide) (by decide)) (inv.frameOffset_ne 232 64 (by decide) (by decide) (by decide)) (inv.frameOffset_ne 232 184 (by decide) (by decide) (by decide)) inv.capCell
  have h_pushBaseDomain : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 8) := by rw [opAddREntry_memaddrs]; exact inv.headerDomain 8 (by simp [guestHeaderOffsets])
  have h_pushBaseCell : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 8) = .word base := opAddREntry_memory_base s frame sp base xv yv funding a0 a1 a2 a3 b0 b1 b2 b3 h8 (inv.frameOffset_ne 8 64 (by decide) (by decide) (by decide)) (inv.frameOffset_ne 8 184 (by decide) (by decide) (by decide)) inv.baseCell
  have h_below : (sp - 2).toNat < cap.toNat := sp_sub_two_below_cap sp cap inv.spLower inv.spLeCap
  have h_notFull : (sp - 2) ≠ (1024 : BitVec 64) := sp_sub_two_ne_1024 sp cap h_below inv.capBound
  have h_storeDomain0 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (base + (sp - 2) * 32) := by rw [opAddREntry_memaddrs]; simpa [operandAddress] using inv.yDomain0
  have h_storeDomain1 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (base + (sp - 2) * 32 + 8) := by rw [opAddREntry_memaddrs]; simpa [operandAddress] using inv.yDomain1
  have h_storeDomain2 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (base + (sp - 2) * 32 + 8 + 8) := by rw [opAddREntry_memaddrs]; simpa [operandAddress, BitVec.add_assoc] using inv.yDomain2
  have h_storeDomain3 : (opAddREntry s frame sp (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (base + (sp - 2) * 32 + 8 + 8 + 8) := by rw [opAddREntry_memaddrs]; simpa [operandAddress, BitVec.add_assoc] using inv.yDomain3
  have h_clockP : (opAddPushState s frame sp cap base (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).clock ≠ 0 := by have := inv.clock; rw [opAddPushState_clock, opAddREntry_clock, opAddGasState_clock, opAddYEntry_clock]; omega
  have h_pcDomain : (opAddPushState s frame sp cap base (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memaddrs (frame + 0) := inv.headerDomain 0 (by simp [guestHeaderOffsets])
  have h_pcCell : (opAddPushState s frame sp cap base (fourWordValue a0 a1 a2 a3) (fourWordValue b0 b1 b2 b3) funding a0 a1 a2 a3 b0 b1 b2 b3).memory (frame + 0) = .word pc := by
    simpa [xv, yv] using opAddPushState_memory_pc s frame sp cap base pc xv yv funding a0 a1 a2 a3 b0 b1 b2 b3 hframe16 hs0 hs1 hs2 hs3
      (opAddREntry_memory_frame s frame sp pc xv yv funding a0 a1 a2 a3 b0 b1 b2 b3 hframe16 hframe64 hframe184 (by simpa using inv.pcCell))
  exact opAdd_body_run coeff s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3
    h_installed
    h_hFrame
    h_clock0
    h_spDomain
    h_spCell
    h_nonzero
    h_baseDomain
    h_baseCell
    h_xDomain0
    h_xDomain1
    h_xDomain2
    h_xDomain3
    h_xCell0
    h_xCell1
    h_xCell2
    h_xCell3
    h_clockX
    h_nonzeroY
    h_spYDomain
    h_spYCell
    h_baseYDomain
    h_baseYCell
    h_yDomain0
    h_yDomain1
    h_yDomain2
    h_yDomain3
    h_yCell0
    h_yCell1
    h_yCell2
    h_yCell3
    h_clockY
    h_fundingY
    h_enough
    h_gasLeftDomain
    h_gasUsedDomain
    h_clockZ
    h_clockR
    h_pushSpDomain
    h_pushSpCell
    h_capDomain
    h_capCell
    h_pushBaseDomain
    h_pushBaseCell
    h_below
    h_notFull
    h_storeDomain0
    h_storeDomain1
    h_storeDomain2
    h_storeDomain3
    h_clockP
    h_pcDomain
    h_pcCell

#print axioms opAdd_body_run_of_frame

end InitECandidate.Runtime.FineCost
