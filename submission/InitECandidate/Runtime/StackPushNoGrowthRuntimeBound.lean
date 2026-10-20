import InitECandidate.Runtime.EvmMemoryOperandContext
import InitECandidate.Runtime.EvmOperandStackSource
import InitECandidate.Runtime.OriginalStackPushInstalled
import InitECandidate.Runtime.RunBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Actual stack_push costs no body clocks when the two real header loads
establish the no-growth guard. Invalid later reads/writes still terminate. -/
theorem stack_push_no_growth_body_bounded {F : Type}
 (s : PanSemStateFiniteExact 64 F) (frame index capacity : BitVec 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (indexDomain : s.memaddrs (frame+16)) (indexAt : s.memory (frame+16)=.word index)
 (capacityDomain : s.memaddrs (frame+232)) (capacityAt : s.memory (frame+232)=.word capacity)
 (inside : index.toNat<capacity.toNat) (code : s.code=originalRuntimeCode) :
 RunBounded s (sourceFunctionBody Guest.guestFn_stack_push) 0 := by
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (stackPushAt 0) 0
 rw [source_stack_push_0]
 apply RunBounded.decWord s (ofString "sp") (.load .one (fundingAddress 16)) index (eval_fundingLoad s frame (16#64) index atFrame indexDomain indexAt)
 let first:=setVarHOLFinite (ofString "sp") (.val (.word index)) s
 change RunBounded first (stackPushAt 1) 0
 rw [source_stack_push_1]
 apply RunBounded.decWord first (ofString "cap") (.load .one (fundingAddress 232)) capacity (eval_fundingLoad first frame (232#64) capacity atFrame capacityDomain capacityAt)
 let second:=setVarHOLFinite (ofString "cap") (.val (.word capacity)) first
 change RunBounded second (stackPushAt 2) 0
 have condition : @evalHOLExact 64 F _ second.toExact (fun a=>Classical.propDecidable (second.memaddrs a)) (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap")))=some (.val (.word 0)) := by
  simp (config:={decide:=true}) [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,evalHOLExact,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside]
 let growth:=match stackPushAt 2 with | .seq (.ite _ branch _) _=>branch | _=>.skip
 have skipped : evaluateHOLFiniteState second (.ite (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap"))) growth .skip)=(none,second) := by
  rw [evaluateHOLFiniteState_ite,condition]
  simp [evaluateHOLFiniteState_skip]
 have left : RunBounded second (.ite (.cmp .notLower (.var .local (ofString "sp")) (.var .local (ofString "cap"))) growth .skip) 0 := by unfold RunBounded;rw [skipped];simp
 rw [source_stack_push_2]
 apply RunBounded.seq (a:=0) (b:=0) left (by omega)
 intro next normal nextCode nextBudget
 have equal : next=second:=(Prod.mk.inj (normal.symm.trans skipped)).2
 subst next
 exact RunBounded.ofProg (ProgBounded.straight (stackPushAt 3) (by decide_cbv)) code (by omega)
/-- Actual installed nongrowing push, at any destination and arbitrary source
arguments, costs one clock including failed argument/shape/access paths. -/
theorem stack_push_no_growth_call_bounded {F : Type}
 (s : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (code : s.code=originalRuntimeCode) (budget : 1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "stack_push") arguments) 1 := by
 cases args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments with
 | none=>unfold RunBounded;rw [evaluateHOLFiniteState_call,args];simp
 | some values=>
  apply RunBounded.call (bodyCost:=0) args budget
  intro body callee returnShape lookup
  have installed : s.code.lookup (ofString "stack_push")=some ([(ofString "v",.comb [.one,.one,.one,.one])],sourceFunctionBody Guest.guestFn_stack_push,.one) := by rw [code];exact originalRuntimeCode_stackPush_lookup
  have equal:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "stack_push") [(ofString "v",.comb [.one,.one,.one,.one])] (sourceFunctionBody Guest.guestFn_stack_push) body .one returnShape values callee installed lookup
  subst body
  exact stack_push_no_growth_body_bounded (callEntryStateHOLFinite s callee) frame words.stackSize words.stackCapacity valid.ev (valid.headerDomain 16 (by simp)) valid.stackSize (valid.headerDomain 232 (by simp)) valid.stackCapacity inside code
#print axioms stack_push_no_growth_body_bounded
#print axioms stack_push_no_growth_call_bounded
end InitECandidate.Runtime
