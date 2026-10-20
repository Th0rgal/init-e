import InitECandidate.Runtime.CreateFundingReservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def opCallAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_op_call)
def GasFunding.callReserved (funding : GasFunding) (allocated : BitVec 64) : GasFunding:=
 {funding with used:=funding.used-allocated}

theorem source_op_call_29 : opCallAt 29=.seq
 (.store (.op .add [.var .global (ofString "ev"),.const 184])
  (.op .sub [.load .one (.op .add [.var .global (ofString "ev"),.const 184]),.rfield 1 (.var .local (ofString "mcg"))])) (opCallAt 30):=rfl

theorem GasFunding.callReserved_potential (funding : GasFunding) (allocated : BitVec 64) (enough : allocated≤funding.used) :
 (funding.callReserved allocated).potential+(childFunding allocated).potential=funding.potential := by
 have debit:=gasDebit_toNat funding.used allocated enough
 simp only [GasFunding.callReserved,GasFunding.potential,childFunding]
 rw [debit]
 have allocatedBound:=BitVec.le_def.mp enough
 change funding.left.toNat+(funding.used.toNat-allocated.toNat)+funding.spilled.toNat+(allocated.toNat+0+0)=_
 omega

/-- Actual op_call removes the child allocation from gas-used immediately
following charge_gas. Until child construction/refund this is pending funding,
not discarded credit; allocation sufficiency is an explicit arithmetic duty. -/
theorem op_call_actual_reservation_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record charged allocated : BitVec 64) (funding : GasFunding) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word record)))
 (atFunding : HasGasFunding s record funding) (readable : s.memaddrs (record+184))
 (atMessageGas : s.locals.lookup (ofString "mcg")=some (.rStruct [.val (.word charged),.val (.word allocated)]))
 (run : evaluateHOLFiniteState s (opCallAt 29)=(some (.returned value),post)) :
 evaluateHOLFiniteState (sourceWriteWord s (record+184) (funding.used-allocated)) (opCallAt 30)=(some (.returned value),post) ∧
 HasGasFunding (sourceWriteWord s (record+184) (funding.used-allocated)) record (funding.callReserved allocated) ∧
 (∀watched : BitVec 64,watched≠record+184 → (sourceWriteWord s (record+184) (funding.used-allocated)).memory watched=s.memory watched) := by
 rw [source_op_call_29] at run
 obtain ⟨stored,normal,tailRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) s v) run
 have destination : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .add [.var .global (ofString "ev"),.const 184])=some (.val (.word (record+184))) := by
  simp [evalHOLExact,evalListHOLExact,atCurrent,wordOpHOL,wordOp,valueIsWord,valueWord]
 have loaded : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (.op .add [.var .global (ofString "ev"),.const 184]))=some (.val (.word funding.used)) := by
  rw [evalHOLExact,destination]
  simp [toExact,isWfShapeExactHOL,memLoadHOLExact,readable,atFunding.2.1]
  exact ⟨readable,atFunding.2.1⟩
 have expression : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.op .sub [.load .one (.op .add [.var .global (ofString "ev"),.const 184]),.rfield 1 (.var .local (ofString "mcg"))])=some (.val (.word (funding.used-allocated))) := by
  rw [evalHOLExact]
  simp only [evalListHOLExact,loaded]
  simp [evalHOLExact,atMessageGas,wordOpHOL,wordOp,valueIsWord,valueWord]
 have storedEq:=store_normal_exact s stored _ _ (record+184) (funding.used-allocated) destination expression normal
 subst stored
 refine ⟨tailRun,?_,?_⟩
 · simp [HasGasFunding,GasFunding.callReserved,sourceWriteWord]
   exact ⟨atFunding.1,atFunding.2.2⟩
 · intro watched different
   change watched≠record+184#64 at different
   simp [sourceWriteWord,different]
#print axioms source_op_call_29
#print axioms GasFunding.callReserved_potential
#print axioms op_call_actual_reservation_returned
end InitECandidate.Runtime
