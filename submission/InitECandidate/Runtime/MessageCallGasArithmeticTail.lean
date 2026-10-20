import InitECandidate.Runtime.CallFundingReservation
import InitECandidate.Runtime.FundingWordDeclarationReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def messageCallGasAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_calculate_message_call_gas)
def messageCallForward (requested available : BitVec 64) : BitVec 64:=
 if available.toNat<requested.toNat then available else requested

theorem source_message_call_gas_5 : messageCallGasAt 5=
 .dec (ofString "avail") .one (.op .sub [.op .sub [.var .local (ofString "gas_left"),.var .local (ofString "memory_cost")],.var .local (ofString "extra_gas")])
 (.dec (ofString "mx") .one (.op .sub [.var .local (ofString "avail"),.shift .lsr (.var .local (ofString "avail")) (.const 6)])
 (.dec (ofString "g") .one (.var .local (ofString "gas"))
 (.seq (.ite (.cmp .lower (.var .local (ofString "mx")) (.var .local (ofString "g"))) (.assign .local (ofString "g") (.var .local (ofString "mx"))) .skip)
 (.return (.rstruct [.op .add [.var .local (ofString "g"),.var .local (ofString "extra_gas")],.op .add [.var .local (ofString "g"),.var .local (ofString "stipend")]]))))) := rfl

/-- Exact original arithmetic suffix when source CALL passes zero memory and
extra costs. No argument about the helper's execution is supplied. -/
theorem message_call_gas_arithmetic_tail_result {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (requested remaining stipend : BitVec 64) (value : ValueHOL 64)
 (atRequested : s.locals.lookup (ofString "gas")=some (.val (.word requested)))
 (atRemaining : s.locals.lookup (ofString "gas_left")=some (.val (.word remaining)))
 (atMemory : s.locals.lookup (ofString "memory_cost")=some (.val (.word (0#64))))
 (atExtra : s.locals.lookup (ofString "extra_gas")=some (.val (.word (0#64))))
 (atStipend : s.locals.lookup (ofString "stipend")=some (.val (.word stipend)))
 (run : evaluateHOLFiniteState s (messageCallGasAt 5)=(some (.returned value),post)) :
 value=.rStruct [.val (.word (messageCallForward requested (createGasAllocation remaining))),
 .val (.word (messageCallForward requested (createGasAllocation remaining)+stipend))] := by
 have source5 : messageCallGasAt 5=.dec (ofString "avail") .one (.op .sub [.op .sub [.var .local (ofString "gas_left"),.var .local (ofString "memory_cost")],.var .local (ofString "extra_gas")]) (messageCallGasAt 6):=rfl
 have source6 : messageCallGasAt 6=.dec (ofString "mx") .one (.op .sub [.var .local (ofString "avail"),.shift .lsr (.var .local (ofString "avail")) (.const 6)]) (messageCallGasAt 7):=rfl
 have source7 : messageCallGasAt 7=.dec (ofString "g") .one (.var .local (ofString "gas")) (messageCallGasAt 8):=rfl
 have source8 : messageCallGasAt 8=.seq (.ite (.cmp .lower (.var .local (ofString "mx")) (.var .local (ofString "g"))) (.assign .local (ofString "g") (.var .local (ofString "mx"))) .skip) (messageCallGasAt 9):=rfl
 have source9 : messageCallGasAt 9=.return (.rstruct [.op .add [.var .local (ofString "g"),.var .local (ofString "extra_gas")],.op .add [.var .local (ofString "g"),.var .local (ofString "stipend")]]):=rfl
 rw [source5] at run
 obtain ⟨avail,firstOutput,availEval,firstRun,firstScope⟩:=funding_declaration_returned_context run
 have availEq : avail=.val (.word remaining) := by
  simpa [evalHOLExact,evalListHOLExact,atRemaining,atMemory,atExtra,wordOpHOL,wordOp,valueIsWord,valueWord] using availEval.symm
 subst avail
 let first:=setVarHOLFinite (ofString "avail") (.val (.word remaining)) s
 change evaluateHOLFiniteState first (messageCallGasAt 6)=_ at firstRun
 rw [source6] at firstRun
 obtain ⟨maximum,secondOutput,maximumEval,secondRun,secondScope⟩:=funding_declaration_returned_context firstRun
 have maximumEq : maximum=.val (.word (createGasAllocation remaining)) := by
  simpa [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,wordShiftHOL,createGasAllocation] using maximumEval.symm
 subst maximum
 let second:=setVarHOLFinite (ofString "mx") (.val (.word (createGasAllocation remaining))) first
 change evaluateHOLFiniteState second (messageCallGasAt 7)=_ at secondRun
 rw [source7] at secondRun
 obtain ⟨requestedValue,thirdOutput,requestedEval,thirdRun,thirdScope⟩:=funding_declaration_returned_context secondRun
 have requestedEq : requestedValue=.val (.word requested) := by
  simpa (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,atRequested] using requestedEval.symm
 subst requestedValue
 let third:=setVarHOLFinite (ofString "g") (.val (.word requested)) second
 change evaluateHOLFiniteState third (messageCallGasAt 8)=_ at thirdRun
 rw [source8] at thirdRun
 obtain ⟨chosen,normal,returned⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) third v) thirdRun
 rw [evaluateHOLFiniteState_ite] at normal
 by_cases lower : (createGasAllocation remaining).toNat<requested.toNat
 · have chosenEq : chosen=setVarHOLFinite (ofString "g") (.val (.word (createGasAllocation remaining))) third := by
    have normalized:=lower
    simp only [createGasAllocation,BitVec.toNat_sub,BitVec.toNat_ushiftRight] at normalized
    simp (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,createGasAllocation,normalized] at normal
    simp [isValidValueHOLExact,lookupKvarHOLExact,shapeOfHOLExact,shapeEqHOL,HolFiniteMapExact.lookup_update,FUPDATE] at normal
    simpa [third,second,first,setVarHOLFinite,setKvarHOLFinite,createGasAllocation] using normal.symm
   subst chosen
   rw [source9,evaluateHOLFiniteState_return] at returned
   have normalized:=lower
   simp only [createGasAllocation,BitVec.toNat_sub,BitVec.toNat_ushiftRight] at normalized
   simpa (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,atExtra,atStipend,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL,messageCallForward,createGasAllocation,normalized] using (Prod.mk.inj returned).1.symm
 · have chosenEq : chosen=third := by
    have normalized:=lower
    simp only [createGasAllocation,BitVec.toNat_sub,BitVec.toNat_ushiftRight] at normalized
    simp (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,createGasAllocation,normalized] at normal
    exact normal.symm
   subst chosen
   rw [source9,evaluateHOLFiniteState_return] at returned
   have normalized:=lower
   simp only [createGasAllocation,BitVec.toNat_sub,BitVec.toNat_ushiftRight] at normalized
   simpa (config:={decide:=true}) [third,second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,evalListHOLExact,atExtra,atStipend,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL,messageCallForward,createGasAllocation,normalized] using (Prod.mk.inj returned).1.symm

/-- The final real gas tuple has bounded stipend excess and no word wrap
under a funded interpreter's current regular-gas ceiling. -/
theorem message_call_gas_arithmetic_tail_ceiling {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (requested remaining stipend : BitVec 64) (value : ValueHOL 64)
 (atRequested : s.locals.lookup (ofString "gas")=some (.val (.word requested)))
 (atRemaining : s.locals.lookup (ofString "gas_left")=some (.val (.word remaining)))
 (atMemory : s.locals.lookup (ofString "memory_cost")=some (.val (.word (0#64))))
 (atExtra : s.locals.lookup (ofString "extra_gas")=some (.val (.word (0#64))))
 (atStipend : s.locals.lookup (ofString "stipend")=some (.val (.word stipend)))
 (funded : remaining.toNat≤200000000) (stipendBound : stipend.toNat≤2300)
 (run : evaluateHOLFiniteState s (messageCallGasAt 5)=(some (.returned value),post)) :
 ∃forwarded allocated : BitVec 64,value=.rStruct [.val (.word forwarded),.val (.word allocated)] ∧
 forwarded≤remaining ∧allocated.toNat=forwarded.toNat+stipend.toNat ∧allocated.toNat≤forwarded.toNat+2300 := by
 have result:=message_call_gas_arithmetic_tail_result s post requested remaining stipend value atRequested atRemaining atMemory atExtra atStipend run
 let forwarded:=messageCallForward requested (createGasAllocation remaining)
 have below : forwarded≤createGasAllocation remaining := by
  apply BitVec.le_def.mpr
  dsimp [forwarded,messageCallForward]
  split <;>omega
 have available:=BitVec.le_def.mp (createGasAllocation_le remaining)
 have forwardBound:=BitVec.le_def.mp below
 have noWrap : forwarded.toNat+stipend.toNat<2^64:=by omega
 refine ⟨forwarded,forwarded+stipend,result,BitVec.le_def.mpr (by omega),?_,?_⟩
 · exact BitVec.toNat_add_of_lt noWrap
 · rw [BitVec.toNat_add_of_lt noWrap]
   omega
#print axioms source_message_call_gas_5
#print axioms message_call_gas_arithmetic_tail_result
#print axioms message_call_gas_arithmetic_tail_ceiling
end InitECandidate.Runtime
