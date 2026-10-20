import InitECandidate.Runtime.EvmStackPopSource
import InitECandidate.Runtime.FundingAssignReturnedContext
import InitECandidate.Runtime.TrapNoReturn
import InitECandidate.Runtime.VmFn_stack_pop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The whole real stack_pop only decrements its real counter on any actual
returned path. Its underflow branch cannot return; no callee/read success assumed. -/
theorem stack_pop_body_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (frame index : BitVec 64) (value : ValueHOL 64)
 (atFrame : s.globals.lookup (ofString "ev")=some (.val (.word frame)))
 (domain : s.memaddrs (frame+16)) (indexAt : s.memory (frame+16)=.word index)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_stack_pop)=(some (.returned value),post)) :
 0<index.toNat ∧post.memory=(sourceWriteWord s (frame+16) (index-1)).memory ∧
 post.globals=s.globals ∧post.clock=s.clock ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (stackPopAt 0)=_ at run
 have metadata:=evaluateHOLFiniteState_metadata s (stackPopAt 0)
 have clock:=clockPreserving_of_extStraightLine (stackPopAt 0) (by decide_cbv) s
 rw [run] at metadata clock
 rw [source_stack_pop_0] at run
 obtain ⟨loaded,output,evaluated,nextRun,scope⟩:=funding_declaration_returned_context run
 have exactLoad:=eval_fundingLoad s frame (16#64) index atFrame domain indexAt
 have equal : loaded=.val (.word index):=Option.some.inj (evaluated.symm.trans exactLoad)
 subst loaded
 let first:=setVarHOLFinite (ofString "sp") (.val (.word index)) s
 change evaluateHOLFiniteState first (stackPopAt 1)=_ at nextRun
 have atIndex : first.locals.lookup (ofString "sp")=some (.val (.word index)) := by
  simp [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have nonzero : index≠0#64 := by
  intro zero
  have condition : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
   (.cmp .equal (.var .local (ofString "sp")) (.const 0))=some (.val (.word 1)) := by
   simp [evalHOLExact,atIndex,zero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_stack_pop_1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition] at nextRun
  have noNormal : (evaluateHOLFiniteState first (.raise (ofString "EvmErr") (.const 2))).1≠none := by
   rw [evaluateHOLFiniteState_raise]
   split
   · dsimp only;split <;>simp
   · simp
  have noReturn:=evaluate_raise_no_return first (ofString "EvmErr") (.const 2) value
  cases raised : evaluateHOLFiniteState first (.raise (ofString "EvmErr") (.const 2)) with
  | mk result next=>
   rw [raised] at nextRun noNormal noReturn
   cases result with
   | none=>exact noNormal rfl
   | some r=>exact noReturn (Prod.mk.inj nextRun).1
 have condition : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
  (.cmp .equal (.var .local (ofString "sp")) (.const 0))=some (.val (.word 0)) := by
  simp [evalHOLExact,atIndex,nonzero,Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_stack_pop_1,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,condition] at nextRun
 simp only [if_pos rfl,evaluateHOLFiniteState_skip] at nextRun
 change evaluateHOLFiniteState first (stackPopAt 2)=_ at nextRun
 have decrement : @evalHOLExact 64 F _ first.toExact (fun a=>Classical.propDecidable (first.memaddrs a))
  (.op .sub [.var .local (ofString "sp"),.const 1])=some (.val (.word (index-1#64))) := by
  simp [evalHOLExact,evalListHOLExact,atIndex,wordOpHOL,wordOp,valueIsWord,valueWord]
 rw [source_stack_pop_2] at nextRun
 have storeRun:=funding_assignment_returned_context first output .local (ofString "sp") _ (index-1#64) (stackPopAt 3) value decrement nextRun
 let second:=setKvarHOLFinite .local (ofString "sp") (.val (.word (index-1#64))) first
 change evaluateHOLFiniteState second (stackPopAt 3)=_ at storeRun
 have nextIndex : second.locals.lookup (ofString "sp")=some (.val (.word (index-1#64))) := by
  simp [second,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 rw [source_stack_pop_3] at storeRun
 have finalRun:=funding_store_returned_context second output (fundingAddress 16) (.var .local (ofString "sp")) (frame+16) (index-1#64) (stackPopAt 4) value (eval_fundingAddress second frame 16 atFrame) (by simpa [evalHOLExact] using nextIndex) storeRun
 let written:=sourceWriteWord second (frame+16) (index-1#64)
 change evaluateHOLFiniteState written (stackPopAt 4)=_ at finalRun
 have memory:=evaluate_readOnly_memory (stackPopAt 4) (by decide_cbv) written
 have globals:=evaluate_readOnly_globals (stackPopAt 4) (by decide_cbv) written
 rw [finalRun] at memory globals
 have positive : 0<index.toNat := by
  have different : index.toNat≠0 := by intro zero;apply nonzero;apply BitVec.eq_of_toNat_eq;exact zero
  omega
 refine ⟨positive,?_,?_,clock,metadata.2.1,metadata.2.2.1,metadata.1⟩
 · rw [scope,memory];rfl
 · rw [scope,globals];rfl
#print axioms stack_pop_body_returned_frame
end InitECandidate.Runtime
