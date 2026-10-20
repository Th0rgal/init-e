import InitECandidate.Runtime.EvmOperandStackWriteSuffix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The actual original stack_push no-growth path: both real guards skip,
exactly four owned operand words and the stack counter are written, and no
source clock is consumed in its body. -/
theorem stack_push_no_growth_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame base index capacity a b c d : BitVec 64) (value : ValueHOL 64)
 (atCurrent : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (headerDomain : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (frame+offset))
 (baseAt : s.memory (frame+8)=.word base) (indexAt : s.memory (frame+16)=.word index)
 (capacityAt : s.memory (frame+232)=.word capacity)
 (inside : index.toNat<capacity.toNat) (capacityBound : capacity.toNat≤1024)
 (destinations : ∀offset∈([0,8,16,24] : List (BitVec 64)),s.memaddrs (base+index*32+offset))
 (run : evaluateHOLFiniteState s (stackPushAt 0)=(some (.returned value),post)) :
 value=.val (.word 0) ∧post.memory=(stackPushWritePost s frame base index a b c d).memory ∧
 post.globals=s.globals ∧post.clock=s.clock ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 have metadata:=evaluateHOLFiniteState_metadata s (stackPushAt 0)
 rw [run] at metadata
 rw [source_stack_push_0] at run
 obtain ⟨indexValue,firstOutput,indexEval,firstRun,firstScope⟩:=funding_declaration_returned_context run
 have loadedIndex:=eval_fundingLoad s frame (16#64) index atCurrent (headerDomain 16 (by simp)) indexAt
 have indexEq : indexValue=.val (.word index):=Option.some.inj (indexEval.symm.trans loadedIndex)
 subst indexValue
 let first:=setVarHOLFinite (ofString "sp") (.val (.word index)) s
 change evaluateHOLFiniteState first (stackPushAt 1)=_ at firstRun
 rw [source_stack_push_1] at firstRun
 obtain ⟨capacityValue,secondOutput,capacityEval,secondRun,secondScope⟩:=funding_declaration_returned_context firstRun
 have loadedCapacity:=eval_fundingLoad first frame (232#64) capacity atCurrent (headerDomain 232 (by simp)) capacityAt
 have capacityEq : capacityValue=.val (.word capacity):=Option.some.inj (capacityEval.symm.trans loadedCapacity)
 subst capacityValue
 let second:=setVarHOLFinite (ofString "cap") (.val (.word capacity)) first
 change evaluateHOLFiniteState second (stackPushAt 2)=_ at secondRun
 rw [source_stack_push_2] at secondRun
 obtain ⟨afterGrowth,normalGrowth,nextRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) second v) secondRun
 have growthCondition : @evalHOLExact 64 F _ second.toExact (fun address=>Classical.propDecidable (second.memaddrs address))
  (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))=some (.val (.word 0)) := by
  simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside]
 rw [evaluateHOLFiniteState_ite,growthCondition] at normalGrowth
 change evaluateHOLFiniteState second .skip=(none,afterGrowth) at normalGrowth
 rw [evaluateHOLFiniteState_skip] at normalGrowth
 have growthEq : afterGrowth=second := (Prod.mk.inj normalGrowth).2.symm
 subst afterGrowth
 rw [source_stack_push_3] at nextRun
 obtain ⟨afterLimit,normalLimit,writeRun⟩:=seq_returned_of_nonreturning_first (by intro v;exact evaluate_noDirectReturn _ (by decide_cbv) second v) nextRun
 have notLimit : index≠1024#64 := by intro equal;have natural:=congrArg BitVec.toNat equal;change index.toNat=1024 at natural;omega
 have limitCondition : @evalHOLExact 64 F _ second.toExact (fun address=>Classical.propDecidable (second.memaddrs address))
  (.cmp .equal (.var .local (ofString "sp")) (.const 1024))=some (.val (.word 0)) := by
  simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,notLimit]
 rw [evaluateHOLFiniteState_ite,limitCondition] at normalLimit
 change evaluateHOLFiniteState second .skip=(none,afterLimit) at normalLimit
 rw [evaluateHOLFiniteState_skip] at normalLimit
 have limitEq : afterLimit=second := (Prod.mk.inj normalLimit).2.symm
 subst afterLimit
 have secondIndex : second.locals.lookup (ofString "sp")=some (.val (.word index)) := by simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have secondValue : second.locals.lookup (ofString "v")=some (fundingU256 a b c d) := by simpa (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atValue
 obtain ⟨returned,outputEq⟩:=stack_push_write_suffix_returned second secondOutput frame base index a b c d value atCurrent secondIndex secondValue (headerDomain 8 (by simp)) baseAt destinations writeRun
 refine ⟨returned,?_,?_,?_,metadata.2.1,metadata.2.2.1,metadata.1⟩
 all_goals rw [firstScope,secondScope,outputEq];rfl
#print axioms stack_push_no_growth_returned
end InitECandidate.Runtime
