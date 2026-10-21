import InitECandidate.Runtime.OpPopContinuation
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open GuestFrameInvariant

set_option maxHeartbeats 4000000

/-- Full actual `op_pop` body execution from the frame invariant: the installed
`stack_pop` helper runs, then the checked charge/pc/return continuation. -/
theorem opPop_body_run
    (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp cap base pc : BitVec 64) (funding : GasFunding)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (inv : GuestFrameInvariant s frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3)
    (clockTwenty : 20 ≤ s.clock) :
    ∃ post events, StatementRun s (sourceFunctionBody Guest.guestFn_op_pop)
      (some (.returned (.val (.word (0 : BitVec 64))))) post events := by
  classical
  let entry := callEntryStateHOLFinite s HolFiniteMapExact.empty
  let xv : ValueHOL 64 := .rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]
  let bodyPost := { emptyLocalsHOLFinite (stackPopStored entry frame sp) with
    locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite (stackPopStored entry frame sp)).locals
      (ofString "sp", entry.locals.lookup (ofString "sp")) }
  have invEntry : GuestFrameInvariant entry frame sp cap base pc funding a0 a1 a2 a3 b0 b1 b2 b3 := by
    apply inv.callEntry_GuestFrameInvariant
    simp [entry, callEntryStateHOLFinite]
    omega
  have hFrameEntry : entry.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [entry, callEntryStateHOLFinite] using inv.ev
  have spDomainEntry : entry.memaddrs (frame + 16) := by simpa [entry, callEntryStateHOLFinite] using inv.headerDomain 16 (by simp [guestHeaderOffsets])
  have spCellEntry : entry.memory (frame + 16) = .word sp := by simpa [entry, callEntryStateHOLFinite] using inv.spCell
  have baseDomainEntry : entry.memaddrs (frame + 8) := by simpa [entry, callEntryStateHOLFinite] using inv.headerDomain 8 (by simp [guestHeaderOffsets])
  have baseCellEntry : entry.memory (frame + 8) = .word base := by simpa [entry, callEntryStateHOLFinite] using inv.baseCell
  have xD0 : (stackPopStored entry frame sp).memaddrs (base + (sp - 1) * 32) := by
    rw [stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs]; simpa [operandAddress] using inv.xDomain0
  have xD1 : (stackPopStored entry frame sp).memaddrs (base + (sp - 1) * 32 + 8) := by
    rw [stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs]; simpa [operandAddress] using inv.xDomain1
  have xD2 : (stackPopStored entry frame sp).memaddrs (base + (sp - 1) * 32 + 16) := by
    rw [stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs]; simpa [operandAddress] using inv.xDomain2
  have xD3 : (stackPopStored entry frame sp).memaddrs (base + (sp - 1) * 32 + 24) := by
    rw [stackPopStored_memaddrs, callEntryStateHOLFinite_memaddrs]; simpa [operandAddress] using inv.xDomain3
  have xC0 : (stackPopStored entry frame sp).memory (base + (sp - 1) * 32) = .word a0 := by
    rw [stackPopStored_memory_ne entry frame sp _ (by simpa [operandAddress] using inv.operand_ne_header (base + (sp - 1) * 32 + 0) 16 (inv.xBelow 0 (by simp)) (by simp))]; simpa [operandAddress, entry, callEntryStateHOLFinite] using inv.xCell0
  have xC1 : (stackPopStored entry frame sp).memory (base + (sp - 1) * 32 + 8) = .word a1 := by
    rw [stackPopStored_memory_ne entry frame sp _ (by simpa [operandAddress] using inv.operand_ne_header (base + (sp - 1) * 32 + 8) 16 (inv.xBelow 8 (by simp)) (by simp))]; simpa [operandAddress, entry, callEntryStateHOLFinite] using inv.xCell1
  have xC2 : (stackPopStored entry frame sp).memory (base + (sp - 1) * 32 + 16) = .word a2 := by
    rw [stackPopStored_memory_ne entry frame sp _ (by simpa [operandAddress] using inv.operand_ne_header (base + (sp - 1) * 32 + 16) 16 (inv.xBelow 16 (by simp)) (by simp))]; simpa [operandAddress, entry, callEntryStateHOLFinite] using inv.xCell2
  have xC3 : (stackPopStored entry frame sp).memory (base + (sp - 1) * 32 + 24) = .word a3 := by
    rw [stackPopStored_memory_ne entry frame sp _ (by simpa [operandAddress] using inv.operand_ne_header (base + (sp - 1) * 32 + 24) 16 (inv.xBelow 24 (by simp)) (by simp))]; simpa [operandAddress, entry, callEntryStateHOLFinite] using inv.xCell3
  have bodyRun := stackPop_success_run (state := entry) frame sp base a0 a1 a2 a3 hFrameEntry
    spDomainEntry spCellEntry (by have := inv.spLower; bv_omega) baseDomainEntry baseCellEntry
    xD0 xD1 xD2 xD3 xC0 xC1 xC2 xC3
  have hFramePost : bodyPost.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simp [bodyPost, emptyLocalsHOLFinite, stackPopStored_globals, entry, callEntryStateHOLFinite, inv.ev]
  have hclockBody : bodyPost.clock = s.clock - 1 := by
    simp [bodyPost, emptyLocalsHOLFinite, stackPopStored, stackPopAssigned, stackPopEntry,
      setKvarHOLFinite, setVarHOLFinite, entry, callEntryStateHOLFinite]
  have bodyClock : bodyPost.clock ≠ 0 := by rw [hclockBody]; omega
  have bodyClockThree : 3 ≤ bodyPost.clock := by rw [hclockBody]; omega
  have bodyCode : bodyPost.code.lookup = s.code.lookup := by
    simp [bodyPost, emptyLocalsHOLFinite, stackPopStored, stackPopAssigned, stackPopEntry,
      setKvarHOLFinite, setVarHOLFinite, entry, callEntryStateHOLFinite]
  have pcDomain : (setVarHOLFinite (ofString "x") xv { bodyPost with locals := s.locals }).memaddrs (frame + 0) := by
    simpa [bodyPost, emptyLocalsHOLFinite, setVarHOLFinite, stackPopStored_memaddrs, entry, callEntryStateHOLFinite] using inv.headerDomain 0 (by simp [guestHeaderOffsets])
  have pcCell : (setVarHOLFinite (ofString "x") xv { bodyPost with locals := s.locals }).memory (frame + 0) = .word pc := by
    have other : (frame + 0 : BitVec 64) ≠ frame + 16 := inv.frameOffset_ne 0 16 (by simp) (by simp) (by decide)
    simp only [bodyPost, emptyLocalsHOLFinite, setVarHOLFinite]
    rw [stackPopStored_memory_ne entry frame sp (frame + 0) other]
    simpa [entry, callEntryStateHOLFinite] using inv.pcCell
  have fundingMemory : HasGasFunding (setVarHOLFinite (ofString "x") xv { bodyPost with locals := s.locals }) frame funding := by
    refine HasGasFunding.setVar (name := ofString "x") (value := xv) ?_
    refine HasGasFunding.emptyLocals ?_
    exact HasGasFunding.stackPopStored inv.fundingMem
      (inv.frameOffset_ne 64 16 (by simp) (by simp) (by decide))
      (inv.frameOffset_ne 184 16 (by simp) (by simp) (by decide))
      (inv.frameOffset_ne 192 16 (by simp) (by simp) (by decide))
  have leftDomain : (setVarHOLFinite (ofString "x") xv { bodyPost with locals := s.locals }).memaddrs (frame + 64) := by
    simpa [bodyPost, emptyLocalsHOLFinite, setVarHOLFinite, stackPopStored_memaddrs, entry, callEntryStateHOLFinite] using inv.headerDomain 64 (by simp [guestHeaderOffsets])
  have usedDomain : (setVarHOLFinite (ofString "x") xv { bodyPost with locals := s.locals }).memaddrs (frame + 184) := by
    simpa [bodyPost, emptyLocalsHOLFinite, setVarHOLFinite, stackPopStored_memaddrs, entry, callEntryStateHOLFinite] using inv.headerDomain 184 (by simp [guestHeaderOffsets])
  have enough : (2 : BitVec 64) ≤ funding.left := by
    have := inv.enough; bv_omega
  exact opPop_body_run_of_parts s frame sp a0 a1 a2 a3 pc funding inv.code (by have := inv.clock; omega)
    bodyPost (stackPopSuccessEvents entry frame sp (base + (sp - 1) * 32) a0 a1 a2 a3) bodyRun
    hFramePost bodyClock bodyClockThree bodyCode pcDomain pcCell fundingMemory leftDomain usedDomain enough

#print axioms opPop_body_run
end InitECandidate.Runtime.FineCost
