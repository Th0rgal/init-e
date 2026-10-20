import InitECandidate.Runtime.FundingReturnedLocal
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.ThreeWordValueShape
import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def validateTransactionAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_validate_transaction)
private def firstAt (index : Nat) : ProgHOL 64 := match validateTransactionAt index with | .seq first _=>first | _=>.skip
private def guards : List (ProgHOL 64) := [firstAt 2,firstAt 3,firstAt 4,firstAt 5]
private def guardSequence (items : List (ProgHOL 64)) (tail : ProgHOL 64) : ProgHOL 64 := items.foldr .seq tail
private theorem guard_sequence_returned {F : Type} (items : List (ProgHOL 64)) (tail : ProgHOL 64) (key : MlS)
 (supported : ∀item∈items,noDirectReturn item=true ∧avoidsLocal key item=true)
 (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (guardSequence items tail)=(some (.returned value),post)) :
 ∃next,evaluateHOLFiniteState next tail=(some (.returned value),post) ∧next.locals.lookup key=s.locals.lookup key := by
 induction items generalizing s with
 | nil=>exact ⟨s,run,rfl⟩
 | cons item rest ih=>
  have one:=supported item (by simp)
  obtain ⟨middle,normal,returned⟩:=encode_header_seq_returned_of_no_return s post item (guardSequence rest tail) value
   (fun v=>evaluate_noDirectReturn item one.1 s v) run
  have kept:=evaluate_avoidsLocal_flowing key item one.2 s (by rw [normal];exact Or.inl rfl)
  rw [normal] at kept
  obtain ⟨next,tailRun,locals⟩:=ih (by intro other present;exact supported other (by simp [present])) middle returned
  exact ⟨next,tailRun,locals.trans kept⟩

/-- The actual transaction validator's regular intrinsic component is bounded
by its literal 2^24 rejection guard. No decoder/gas/nonce/callee contract is assumed. -/
theorem validate_transaction_returned_regular_cap {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_transaction)=(some (.returned value),post)) :
 ∃regular stateGas floor : BitVec 64,
 value=.rStruct [.val (.word regular),.val (.word stateGas),.val (.word floor)] ∧regular.toNat≤16777216 := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (validateTransactionAt 0)=_ at run
 have stage0 : validateTransactionAt 0=.decCall (ofString "ic") (.comb [.one,.one,.one]) (ofString "calculate_intrinsic_cost")
  [.var .local (ofString "tx"),.var .local (ofString "sender")] (validateTransactionAt 1) := rfl
 rw [stage0] at run
 obtain ⟨values,body,callee,shape,_,_,args,lookup,_⟩:=decCall_returned run
 obtain ⟨initial,bodyPost,output,_,checked,tailRun,_⟩:=evaluate_decCall_checked_returned_exact_scope s post (ofString "ic")
  (ofString "calculate_intrinsic_cost") (.comb [.one,.one,.one]) shape _ values body (validateTransactionAt 1) callee value args lookup run
 obtain ⟨regular,stateGas,floor,rfl⟩:=value_three_words_of_checked_shape initial checked.1
 let entry:=setVarHOLFinite (ofString "ic") (.rStruct [.val (.word regular),.val (.word stateGas),.val (.word floor)])
  {bodyPost with locals:=s.locals}
 have atIc : entry.locals.lookup (ofString "ic")=some (.rStruct [.val (.word regular),.val (.word stateGas),.val (.word floor)]) := by
  simp [entry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have stage1 : validateTransactionAt 1=.dec (ofString "gas") .one
  (.load .one (.op .add [.var .local (ofString "tx"),.const 144])) (validateTransactionAt 2) := rfl
 rw [stage1] at tailRun
 obtain ⟨gasValue,inner,_,bodyRun,_⟩:=dec_returned_state tailRun
 let gasEntry:=setVarHOLFinite (ofString "gas") gasValue entry
 have gasIc : gasEntry.locals.lookup (ofString "ic")=some (.rStruct [.val (.word regular),.val (.word stateGas),.val (.word floor)]) := by
  simpa (config:={decide:=true}) [gasEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atIc
 have stagePrefix : validateTransactionAt 2=guardSequence guards (validateTransactionAt 6) := rfl
 rw [stagePrefix] at bodyRun
 have supported : ∀item∈guards,noDirectReturn item=true ∧avoidsLocal (ofString "ic") item=true := by
  intro item member
  simp [guards] at member
  rcases member with rfl|rfl|rfl|rfl <;>decide_cbv
 obtain ⟨capState,capRun,kept⟩:=guard_sequence_returned guards (validateTransactionAt 6) (ofString "ic") supported gasEntry inner value bodyRun
 have capIc:=kept.trans gasIc
 have result:=funding_return_local (validateTransactionAt 6) (ofString "ic") (by decide_cbv) capState inner
  (.rStruct [.val (.word regular),.val (.word stateGas),.val (.word floor)]) value capIc capRun
 refine ⟨regular,stateGas,floor,result,?_⟩
 have stage6 : validateTransactionAt 6=.seq
  (.ite (.cmp .lower (.const 16777216) (.rfield 0 (.var .local (ofString "ic"))))
   (.raise (ofString "TxErr") (.const 63)) .skip) (validateTransactionAt 7) := rfl
 rw [stage6] at capRun
 obtain ⟨middle,normal,_⟩:=encode_header_seq_returned_of_no_return capState inner _ _ value
  (fun v=>evaluate_noDirectReturn _ (by decide_cbv) capState v) capRun
 by_contra tooBig
 have large : 16777216<regular.toNat := by omega
 simp [evaluateHOLFiniteState_ite,evalHOLFinite,evalHOLExact,evalListHOLExact,capIc,
  Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,large,evaluateHOLFiniteState_raise] at normal
 cases exceptionShape : capState.eshapes.lookup (ofString "TxErr") with
 | none=>simp [exceptionShape] at normal
 | some shape=>
  simp only [exceptionShape] at normal
  split at normal <;>simp at normal
#print axioms validate_transaction_returned_regular_cap
end InitECandidate.Runtime
