import InitECandidate.Runtime.FundingAllocationReturnedContext
import InitECandidate.Runtime.GasFunding
import InitECandidate.Runtime.ReturnedStorePlanMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def genericCreateAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_generic_create)
def createGasAllocation (gas : BitVec 64) : BitVec 64:=gas-(gas >>> (6:Nat))
def GasFunding.createReserved (funding : GasFunding) : GasFunding:=
 {funding with left:=funding.left-createGasAllocation funding.left}

theorem source_generic_create_13 : genericCreateAt 13=.dec (ofString "gl") .one
 (.load .one (.op .add [.var .global (ofString "ev"),.const 64])) (genericCreateAt 14):=rfl
theorem source_generic_create_14 : genericCreateAt 14=.dec (ofString "create_gas") .one
 (.op .sub [.var .local (ofString "gl"),.shift .lsr (.var .local (ofString "gl")) (.const 6)]) (genericCreateAt 15):=rfl
theorem source_generic_create_15 : genericCreateAt 15=.seq
 (.store (.op .add [.var .global (ofString "ev"),.const 64]) (.op .sub [.var .local (ofString "gl"),.var .local (ofString "create_gas")])) (genericCreateAt 16):=rfl

theorem createGasAllocation_le (gas : BitVec 64) : createGasAllocation gas≤gas := by
 have shifted : gas >>> (6:Nat)≤gas := by
  apply BitVec.le_def.mpr
  rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  exact Nat.div_le_self _ _
 have natural:=gasDebit_toNat gas (gas >>> (6:Nat)) shifted
 apply BitVec.le_def.mpr
 change (gas-(gas >>> (6:Nat))).toNat≤gas.toNat
 rw [natural]
 omega

theorem GasFunding.createReserved_potential (funding : GasFunding) :
 funding.createReserved.potential+(childFunding (createGasAllocation funding.left)).potential=funding.potential := by
 have debit:=gasDebit_toNat funding.left (createGasAllocation funding.left) (createGasAllocation_le funding.left)
 simp only [GasFunding.createReserved,GasFunding.potential,childFunding]
 rw [debit]
 have allocated:=BitVec.le_def.mp (createGasAllocation_le funding.left)
 change funding.left.toNat-(createGasAllocation funding.left).toNat+funding.used.toNat+funding.spilled.toNat+
  ((createGasAllocation funding.left).toNat+0+0)=funding.left.toNat+funding.used.toNat+funding.spilled.toNat
 omega

/-- The original CREATE reservation declarations and store move real gas
into an explicit pending-child amount. Intervening constructors must retain
this pending funding until the actual child frame exists. -/
theorem generic_create_actual_reservation_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record : BitVec 64) (funding : GasFunding) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word record)))
 (atFunding : HasGasFunding s record funding) (readable : s.memaddrs (record+64))
 (run : evaluateHOLFiniteState s (genericCreateAt 13)=(some (.returned value),post)) :
 ∃ready output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState ready (genericCreateAt 16)=(some (.returned value),output) ∧
 post.memory=output.memory ∧post.globals=output.globals ∧
 HasGasFunding ready record funding.createReserved ∧
 ready.locals.lookup (ofString "create_gas")=some (.val (.word (createGasAllocation funding.left))) ∧
 ready.globals=s.globals ∧ready.memaddrs=s.memaddrs ∧ready.be=s.be ∧ready.code=s.code ∧
 (∀watched : BitVec 64,watched≠record+64 → ready.memory watched=s.memory watched) := by
 rw [source_generic_create_13] at run
 have loaded : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.load .one (.op .add [.var .global (ofString "ev"),.const 64]))=some (.val (.word funding.left)) := by
  simp [evalHOLExact,evalListHOLExact,atCurrent,wordOpHOL,wordOp,valueIsWord,valueWord]
  simp [toExact,isWfShapeExactHOL,memLoadHOLExact,readable,atFunding.1]
  exact ⟨readable,atFunding.1⟩
 obtain ⟨gasValue,firstOutput,evaluated,firstRun,firstScope⟩:=funding_declaration_returned_context run
 have gasValueEq : gasValue=.val (.word funding.left):=Option.some.inj (evaluated.symm.trans loaded)
 subst gasValue
 let first:=setVarHOLFinite (ofString "gl") (.val (.word funding.left)) s
 change evaluateHOLFiniteState first (genericCreateAt 14)=_ at firstRun
 rw [source_generic_create_14] at firstRun
 have allocated : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
  (.op .sub [.var .local (ofString "gl"),.shift .lsr (.var .local (ofString "gl")) (.const 6)])=some (.val (.word (createGasAllocation funding.left))) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,createGasAllocation,wordShiftHOL]
 obtain ⟨allocationValue,secondOutput,evaluatedAllocation,secondRun,secondScope⟩:=funding_declaration_returned_context firstRun
 have allocationEq : allocationValue=.val (.word (createGasAllocation funding.left)):=Option.some.inj (evaluatedAllocation.symm.trans allocated)
 subst allocationValue
 let second:=setVarHOLFinite (ofString "create_gas") (.val (.word (createGasAllocation funding.left))) first
 change evaluateHOLFiniteState second (genericCreateAt 15)=_ at secondRun
 rw [source_generic_create_15] at secondRun
 obtain ⟨stored,normal,tailRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) second v) secondRun
 have destination : @evalHOLExact 64 F _ second.toExact (fun a=>Classical.propDecidable (second.memaddrs a))
  (.op .add [.var .global (ofString "ev"),.const 64])=some (.val (.word (record+64))) := by
  have kept : second.globals.lookup (ofString "ev")=some (.val (.word record)):=atCurrent
  simp [evalHOLExact,evalListHOLExact,kept,wordOpHOL,wordOp,valueIsWord,valueWord]
 have expression : @evalHOLExact 64 F _ second.toExact (fun a=>Classical.propDecidable (second.memaddrs a))
  (.op .sub [.var .local (ofString "gl"),.var .local (ofString "create_gas")])=some (.val (.word (funding.left-createGasAllocation funding.left))) := by
  simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord]
 have storedEq:=store_normal_exact second stored _ _ (record+64) (funding.left-createGasAllocation funding.left) destination expression normal
 subst stored
 refine ⟨_,secondOutput,tailRun,?_,?_,?_,?_,rfl,rfl,rfl,rfl,?_⟩
 · rw [firstScope,secondScope]
 · rw [firstScope,secondScope]
 · simp [HasGasFunding,GasFunding.createReserved,sourceWriteWord,second,first,setVarHOLFinite]
   exact ⟨atFunding.2.1,atFunding.2.2⟩
 · simp [sourceWriteWord,second,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · intro watched different
   change watched≠record+64#64 at different
   simp [sourceWriteWord,different,second,first,setVarHOLFinite]
#print axioms source_generic_create_13
#print axioms source_generic_create_14
#print axioms source_generic_create_15
#print axioms createGasAllocation_le
#print axioms GasFunding.createReserved_potential
#print axioms generic_create_actual_reservation_returned
end InitECandidate.Runtime
