import InitECandidate.Runtime.OpPopCompose
import InitECandidate.Runtime.GuestCostOpAddBody
import InitECandidate.Runtime.GuestFrameOpAdd
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Concrete `op_pop` continuation: `charge_gas 2 ; pc_add 1 ; return 0`. -/
theorem opPop_continuation_run
    (sC : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame pc : BitVec 64) (funding : GasFunding)
    (installed : sC.code.lookup = originalRuntimeCode.lookup)
    (clock : sC.clock ≠ 0) (clockThree : 3 ≤ sC.clock)
    (hFrame : sC.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (leftDomain : sC.memaddrs (frame + 64))
    (usedDomain : sC.memaddrs (frame + 184))
    (memory : HasGasFunding sC frame funding)
    (enough : (2 : BitVec 64) ≤ funding.left)
    (pcDomain : sC.memaddrs (frame + 0))
    (pcCell : sC.memory (frame + 0) = .word pc) :
    ∃ post events, StatementRun sC
      (.seq (.call (some (none, none)) (ofString "charge_gas")
          [.const (2 : BitVec 64)])
        (.seq (.call (some (none, none)) (ofString "pc_add")
            [.const (1 : BitVec 64)])
          (.return (.const (0 : BitVec 64)))))
      (some (.returned (.val (.word (0 : BitVec 64))))) post events := by
  classical
  let entryZ := callEntryStateHOLFinite sC (chargeGasCallee 2)
  let postZ := { chargeGasPost entryZ frame funding.left funding.used (2 : BitVec 64)
    with locals := sC.locals }
  let entryP := callEntryStateHOLFinite postZ (pcAddCallee 1)
  let postP := pcAddSuccessPost entryP frame pc
  let postPL := { postP with locals := postZ.locals }
  have hFrameZ : entryZ.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [entryZ, callEntryStateHOLFinite] using hFrame
  have hAmountZ : entryZ.locals.lookup (ofString "amount") =
      some (.val (.word (2 : BitVec 64))) := by
    simp [entryZ, callEntryStateHOLFinite, chargeGasCallee,
      HolFiniteMapExact.lookup_update_pointwise, FUPDATE]
  have leftDomainZ : entryZ.memaddrs (frame + 64) := by
    simpa [entryZ, callEntryStateHOLFinite] using leftDomain
  have usedDomainZ : entryZ.memaddrs (frame + 184) := by
    simpa [entryZ, callEntryStateHOLFinite] using usedDomain
  have memoryZ : HasGasFunding entryZ frame funding := by
    simpa [entryZ, callEntryStateHOLFinite, HasGasFunding] using memory
  have enoughZ : (2 : BitVec 64) ≤ funding.left := enough
  have chargeBody := chargeGas_body_run_funding entryZ frame (2 : BitVec 64) funding
    hFrameZ hAmountZ leftDomainZ usedDomainZ memoryZ enoughZ
  have chargeArgs : evalListHOLFinite sC (h := fun a => Classical.propDecidable (sC.memaddrs a))
      [.const (2 : BitVec 64)] = some [.val (.word (2 : BitVec 64))] :=
    evalListHOLFinite_singleton_const sC 2
  have chargeLookup : lookupCodeHOLFinite sC.code.lookup (ofString "charge_gas")
      [.val (.word (2 : BitVec 64))] =
      some (sourceFunctionBody Guest.guestFn_charge_gas, chargeGasCallee 2, .one) := by
    simpa [chargeGasCallee] using opAdd_chargeGas_lookup sC.code.lookup installed 2
  have chargePlan : callCostPlan sC (some (none, none)) .one
      (some (.returned (.val (.word (0 : BitVec 64)))))
      (chargeGasPost entryZ frame funding.left funding.used (2 : BitVec 64)) =
      .done none postZ := by
    simp [callCostPlan, postZ, shapeEqHOL, shapeOfHOLExact, shapeEqHOL.shapeEqListHOL]
  have chargeCall := (call_statement_work (coeff := {}) chargeArgs chargeLookup clock
    chargeBody chargePlan).1
  have hFrameP : entryP.globals.lookup (ofString "ev") = some (.val (.word frame)) := by
    simpa [entryP, postZ, entryZ, chargeGasPost, callEntryStateHOLFinite, emptyLocalsHOLFinite,
      setVarHOLFinite, sourceWriteWord, writeWordMemory] using hFrameZ
  have hNP : entryP.locals.lookup (ofString "n") = some (.val (.word (1 : BitVec 64))) := by
    simp [entryP, callEntryStateHOLFinite, pcAddCallee,
      HolFiniteMapExact.lookup_update_pointwise, FUPDATE]
  have pcDomainP : entryP.memaddrs (frame + 0) := by
    simpa [entryP, postZ, entryZ, chargeGasPost, callEntryStateHOLFinite, emptyLocalsHOLFinite,
      setVarHOLFinite, sourceWriteWord, writeWordMemory] using pcDomain
  have pcCellP : entryP.memory (frame + 0) = .word pc := by
    have preserved := chargeGasPost_memory_ne entryZ frame funding.left funding.used
      (2 : BitVec 64) (frame + 0) (Ne.symm (frame_add_zero_ne_64 frame)) (Ne.symm (frame_add_zero_ne_184 frame))
    change (chargeGasPost entryZ frame funding.left funding.used (2 : BitVec 64)).memory (frame + 0) = .word pc
    rw [preserved]
    simpa [entryZ, callEntryStateHOLFinite] using pcCell
  have pcBody := pcAdd_run entryP frame pc 1 hFrameP hNP pcDomainP pcCellP
  have clockP : postZ.clock ≠ 0 := by
    have hpos : 0 < sC.clock - 1 := by omega
    simpa [postZ, chargeGasPost, entryZ, callEntryStateHOLFinite, emptyLocalsHOLFinite,
      setVarHOLFinite, sourceWriteWord, writeWordMemory, Nat.sub_sub] using Nat.ne_of_gt hpos
  have pcArgs : evalListHOLFinite postZ (h := fun a => Classical.propDecidable (postZ.memaddrs a))
      [.const (1 : BitVec 64)] = some [.val (.word (1 : BitVec 64))] :=
    evalListHOLFinite_singleton_const postZ 1
  have pcLookup : lookupCodeHOLFinite postZ.code.lookup (ofString "pc_add")
      [.val (.word (1 : BitVec 64))] =
      some (sourceFunctionBody Guest.guestFn_pc_add, pcAddCallee 1, .one) := by
    simpa [pcAddCallee] using opAdd_pcAdd_lookup postZ.code.lookup installed 1
  have pcPlan : callCostPlan postZ (some (none, none)) .one
      (some (.returned (.val (.word (0 : BitVec 64))))) postP = .done none postPL := by
    simp [callCostPlan, postP, postPL, shapeEqHOL, shapeOfHOLExact, shapeEqHOL.shapeEqListHOL]
  have pcCall := (call_statement_work (coeff := {}) pcArgs pcLookup clockP pcBody pcPlan).1
  have ret : StatementRun postPL (.return (.const (0 : BitVec 64)))
      (some (.returned (.val (.word (0 : BitVec 64))))) (emptyLocalsHOLFinite postPL) _ :=
    StatementRun.returnValue (expression := .const (0 : BitVec 64))
      (costedExpression_events postPL _ _ (by simp [expressionValue, evalHOLExact]))
      (by simp [shapeOfHOLExact, sizeOfShapeWithContextHOL])
  exact ⟨_, _, StatementRun.seqNext chargeCall (StatementRun.seqNext pcCall ret)⟩

/-- `op_pop` body composition from the actual `stack_pop` body run and the checked
`charge_gas 2 ; pc_add 1 ; return 0` continuation. -/
theorem opPop_body_run_of_parts
    (s : PanSemStateFiniteExact 64 Guest.HostMemory)
    (frame sp : BitVec 64) (a0 a1 a2 a3 : BitVec 64) (pc : BitVec 64)
    (funding : GasFunding)
    (installed : s.code.lookup = originalRuntimeCode.lookup)
    (clock : s.clock ≠ 0)
    (bodyPost : PanSemStateFiniteExact 64 Guest.HostMemory)
    (bodyEvents : List WorkEvent)
    (bodyRun : StatementRun (callEntryStateHOLFinite s HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_stack_pop)
      (some (.returned (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])))
      bodyPost bodyEvents)
    (hFramePost : bodyPost.globals.lookup (ofString "ev") = some (.val (.word frame)))
    (bodyClock : bodyPost.clock ≠ 0) (bodyClockThree : 3 ≤ bodyPost.clock)
    (bodyCode : bodyPost.code.lookup = s.code.lookup)
    (pcDomain : (setVarHOLFinite (ofString "x")
      (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])
      { bodyPost with locals := s.locals }).memaddrs (frame + 0))
    (pcCell : (setVarHOLFinite (ofString "x")
      (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])
      { bodyPost with locals := s.locals }).memory (frame + 0) = .word pc)
    (fundingMemory : HasGasFunding (setVarHOLFinite (ofString "x")
      (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])
      { bodyPost with locals := s.locals }) frame funding)
    (leftDomain : (setVarHOLFinite (ofString "x")
      (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])
      { bodyPost with locals := s.locals }).memaddrs (frame + 64))
    (usedDomain : (setVarHOLFinite (ofString "x")
      (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)])
      { bodyPost with locals := s.locals }).memaddrs (frame + 184))
    (enough : (2 : BitVec 64) ≤ funding.left) :
    ∃ post events, StatementRun s (sourceFunctionBody Guest.guestFn_op_pop)
      (some (.returned (.val (.word (0 : BitVec 64))))) post events := by
  classical
  let xv : ValueHOL 64 := .rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]
  let sC := setVarHOLFinite (ofString "x") xv { bodyPost with locals := s.locals }
  obtain ⟨post, contEvents, contRun⟩ := opPop_continuation_run sC frame pc funding
    (by simpa [sC, setVarHOLFinite] using bodyCode.trans installed)
    (by simpa [sC, setVarHOLFinite] using bodyClock)
    (by simpa [sC, setVarHOLFinite] using bodyClockThree)
    (by simpa [sC, setVarHOLFinite] using hFramePost)
    (by simpa [sC] using leftDomain) (by simpa [sC] using usedDomain)
    (by simpa [sC] using fundingMemory) enough
    (by simpa [sC] using pcDomain) (by simpa [sC] using pcCell)
  rw [source_opPop_body]
  refine ⟨_, _, StatementRun.declareCallReturn_cont
    (evalListHOLFinite_nil s) (opAdd_stackPop_lookup s.code.lookup installed) clock bodyRun ?_ contRun⟩
  simp [xv, shapeOfHOLExact, comb4Shape, shapeEqHOL, shapeEqHOL.shapeEqListHOL]

#print axioms opPop_body_run_of_parts

#print axioms opPop_continuation_run
end InitECandidate.Runtime.FineCost
