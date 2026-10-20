import InitECandidate.Runtime.EvmOperandStackSource
import InitECandidate.Runtime.StoreFourWords
import InitECandidate.Runtime.FundingAssignReturnedContext
import InitECandidate.Runtime.U256ZeroFundingValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

noncomputable def stackPushWritePost {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base index a b c d : BitVec 64) : PanSemStateFiniteExact 64 F:=
 sourceWriteWord (journalRecordPost32 s (base+index*32) a b c d) (frame+16) (index+1)

theorem eval_stack_push_base {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base index : BitVec 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atIndex : s.locals.lookup (ofString "sp")=some (.val (.word index)))
 (baseDomain : s.memaddrs (frame+8)) (baseAt : s.memory (frame+8)=.word base) :
 @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) stackPushBase=some (.val (.word (base+index*32))) := by
 have load:=eval_fundingLoad s frame (8#64) base atCurrent baseDomain baseAt
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.load .one (fundingAddress (8#64)))=some (.val (.word base)) at load
 change @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (.op .add [.load .one (fundingAddress (8#64)),.panop .mul [.var .local (ofString "sp"),.const (32#64)]])=_
 rw [evalHOLExact,evalListHOLExact,load]
 simp only [evalListHOLExact]
 simp [evalHOLExact,atIndex,evalListHOLExact,wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord]

/-- The real final structured stack write has exactly four destinations,
then advances only ev16. Its input is the actual four-word ABI value. -/
theorem stack_push_write_suffix_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base index a b c d : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atIndex : s.locals.lookup (ofString "sp")=some (.val (.word index)))
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (baseDomain : s.memaddrs (frame+8)) (baseAt : s.memory (frame+8)=.word base)
 (destinations : ∀offset∈([0,8,16,24] : List (BitVec 64)),s.memaddrs (base+index*32+offset))
 (run : evaluateHOLFiniteState s (stackPushAt 4)=(some (.returned value),post)) :
 value=.val (.word 0) ∧post=emptyLocalsHOLFinite (stackPushWritePost s frame base index a b c d) := by
 rw [source_stack_push_4] at run
 obtain ⟨middle,normal,tailRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) s v) run
 have written:=evaluate_store_four_words s (base+index*32) a b c d stackPushBase (.var .local (ofString "v"))
  (eval_stack_push_base s frame base index atCurrent atIndex baseDomain baseAt) atValue
  (by simpa using destinations 0 (by simp)) (destinations 8 (by simp)) (destinations 16 (by simp)) (destinations 24 (by simp))
 have middleEq : middle=journalRecordPost32 s (base+index*32) a b c d :=(Prod.mk.inj (normal.symm.trans written)).2
 subst middle
 rw [source_stack_push_5] at tailRun
 have increment : @evalHOLExact 64 F _ (journalRecordPost32 s (base+index*32) a b c d).toExact (fun address=>Classical.propDecidable ((journalRecordPost32 s (base+index*32) a b c d).memaddrs address))
  (.op .add [.var .local (ofString "sp"),.const 1])=some (.val (.word (index+1))) := by
  simp [journalRecordPost32,sourceWriteWord,evalHOLExact,evalListHOLExact,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord]
 have finalRun:=funding_store_returned_context (journalRecordPost32 s (base+index*32) a b c d) post (fundingAddress 16) _ (frame+16) (index+1) (stackPushAt 6) value
  (eval_fundingAddress _ frame 16 atCurrent) increment tailRun
 rw [source_stack_push_6] at finalRun
 have result : evaluateHOLFiniteState (stackPushWritePost s frame base index a b c d) (.return (.const 0))=(some (.returned (.val (.word 0))),emptyLocalsHOLFinite (stackPushWritePost s frame base index a b c d)) := by simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
 obtain ⟨returned,postEq⟩:=Prod.mk.inj (finalRun.symm.trans result)
 exact ⟨PanSemResultExact.returned.inj (Option.some.inj returned),postEq⟩

theorem stack_push_write_suffix_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame base index a b c d watched : BitVec 64)
 (differentCounter : watched≠frame+16)
 (differentData : ∀offset∈([0,8,16,24] : List (BitVec 64)),watched≠base+index*32+offset) :
 (stackPushWritePost s frame base index a b c d).memory watched=s.memory watched := by
 have n0:=differentData 0 (by simp)
 have n8:=differentData 8 (by simp)
 have n16:=differentData 16 (by simp)
 have n24:=differentData 24 (by simp)
 change watched≠frame+16#64 at differentCounter
 change watched≠base+index*32#64+0#64 at n0
 change watched≠base+index*32#64+8#64 at n8
 change watched≠base+index*32#64+16#64 at n16
 change watched≠base+index*32#64+24#64 at n24
 simp only [BitVec.add_zero] at n0
 simp [stackPushWritePost,journalRecordPost32,sourceWriteWord,differentCounter,n0,n8,n16,n24]
#print axioms eval_stack_push_base
#print axioms stack_push_write_suffix_returned
#print axioms stack_push_write_suffix_frame
end InitECandidate.Runtime
