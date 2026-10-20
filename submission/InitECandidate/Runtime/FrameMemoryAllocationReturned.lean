import InitECandidate.Runtime.FundingAllocationReturnedContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000
/-- Actual successful upward workspace allocation changes only its global
frontier, returns its old base, and stays below the descending scratch frontier.
Both space guards are consequences of the returned original execution. -/
theorem frame_memory_allocation_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer size scratch : BitVec 64) (value : ValueHOL 64)
 (atPointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)))
 (atScratch : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (atSize : s.locals.lookup (ofString "n")=some (.val (.word size)))
 (ordered : pointer.toNat≤scratch.toNat) (cap : scratch.toNat≤33806089496)
 (code : s.code=originalRuntimeCode)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_frame_mem_alloc)=(some (.returned value),post)) :
 value=.val (.word pointer) ∧
 post.globals=(s.globals.update (ofString "frame_mem_ptr",.val (.word (allocationEnd pointer size)))) ∧
 pointer.toNat+size.toNat≤(allocationEnd pointer size).toNat ∧
 (allocationEnd pointer size).toNat≤scratch.toNat ∧
 (allocationEnd pointer size).toNat%8=0 ∧
 post.memory=s.memory ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧post.clock=s.clock := by
 classical
 rw [source_frame_mem_alloc_body] at run
 obtain ⟨p,innerP,initial,pRun,pPost⟩:=funding_declaration_returned_context run
 have pEq : p=.val (.word pointer) := by simpa [evalHOLExact,atPointer] using initial.symm
 subst p
 let entered:=setVarHOLFinite (ofString "p") (.val (.word pointer)) s
 have pLocal : entered.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have different : ofString "p"≠ofString "n" := by decide
 have nLocal : entered.locals.lookup (ofString "n")=some (.val (.word size)) := by
  simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,atSize]
 change evaluateHOLFiniteState entered frameMemoryAllocationAfterPointer=_ at pRun
 unfold frameMemoryAllocationAfterPointer at pRun
 obtain ⟨afterCheck,checkNormal,qRun⟩:=encode_header_seq_returned_of_no_return entered innerP _ _ value
  (fun v=>evaluate_noDirectReturn _ (by decide_cbv) entered v) pRun
 have checkEval : @evalHOLExact 64 F _ entered.toExact (fun a=>Classical.propDecidable (entered.memaddrs a))
  frameMemoryAllocationRequestCheck=some (.val (.word (if (scratch-pointer).toNat<size.toNat then 1 else 0))) := by
  have global : entered.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) := atScratch
  have sub : @evalHOLExact 64 F _ entered.toExact (fun a=>Classical.propDecidable (entered.memaddrs a))
   (.op .sub [.var .global (ofString "scratch_ptr"),.var .local (ofString "p")])=some (.val (.word (scratch-pointer))) := by
   simp [evalHOLExact,evalListHOLExact,global,pLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  unfold frameMemoryAllocationRequestCheck
  rw [evalHOLExact,sub]
  simp only [evalHOLExact,nLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,decide_eq_true_eq]

 obtain ⟨flag,checkPost⟩:=funding_trap_guard_normal entered afterCheck frameMemoryAllocationRequestCheck _ code checkEval checkNormal
 have request : size.toNat≤(scratch-pointer).toNat := by
  by_contra denied
  have tooBig : (scratch-pointer).toNat<size.toNat := by omega
  have impossible : (1 : BitVec 64)=0 := by simpa only [if_pos tooBig] using flag
  exact (by decide : (1 : BitVec 64)≠0) impossible
 subst afterCheck
 obtain ⟨q,innerQ,endpoint,finishRun,qPost⟩:=funding_declaration_returned_context qRun
 have qEq : q=.val (.word (allocationEnd pointer size)) := by
  have evaluated:=eval_frameMemoryAllocationEndExpression entered pointer size pLocal nLocal
  exact Option.some.inj (evaluated.symm.trans endpoint) |>.symm
 subst q
 let ready:=setVarHOLFinite (ofString "q") (.val (.word (allocationEnd pointer size))) entered
 have qLocal : ready.locals.lookup (ofString "q")=some (.val (.word (allocationEnd pointer size))) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have qp : ofString "q"≠ofString "p" := by decide
 have pReady : ready.locals.lookup (ofString "p")=some (.val (.word pointer)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,qp,pLocal]
 change evaluateHOLFiniteState ready frameMemoryAllocationFinish=_ at finishRun
 unfold frameMemoryAllocationFinish at finishRun
 obtain ⟨afterRound,roundNormal,returnRun⟩:=encode_header_seq_returned_of_no_return ready innerQ _ _ value
  (fun v=>evaluate_noDirectReturn _ (by decide_cbv) ready v) finishRun
 have roundEval : @evalHOLExact 64 F _ ready.toExact (fun a=>Classical.propDecidable (ready.memaddrs a))
  (.cmp .lower (.var .global (ofString "scratch_ptr")) (.var .local (ofString "q")))=
  some (.val (.word (if scratch.toNat<(allocationEnd pointer size).toNat then 1 else 0))) := by
  have global : ready.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) := atScratch
  simp [evalHOLExact,qLocal,global,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
 obtain ⟨roundFlag,roundPost⟩:=funding_trap_guard_normal ready afterRound _ _ code roundEval roundNormal
 have within : (allocationEnd pointer size).toNat≤scratch.toNat := by
  by_contra denied
  have tooBig : scratch.toNat<(allocationEnd pointer size).toNat := by omega
  have impossible : (1 : BitVec 64)=0 := by simpa only [if_pos tooBig] using roundFlag
  exact (by decide : (1 : BitVec 64)≠0) impossible
 subst afterRound
 let assigned:=setKvarHOLFinite .global (ofString "frame_mem_ptr") (.val (.word (allocationEnd pointer size))) ready
 have assignment : evaluateHOLFiniteState ready (.assign .global (ofString "frame_mem_ptr") (.var .local (ofString "q")))=(none,assigned) := by
  have global : ready.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word pointer)) := atPointer
  simp [evaluateHOLFiniteState_assign,evalHOLExact,qLocal,assigned,isValidValueHOLExact,
   lookupKvarHOLExact,global,shapeOfHOLExact,shapeEqHOL]
 have returned : evaluateHOLFiniteState assigned (.return (.var .local (ofString "p")))=
  (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite assigned) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,assigned,setKvarHOLFinite,setGlobalHOLFinite,pReady,shapeOfHOLExact]
 have exactRun:=evaluate_seq_none assignment returned
 obtain ⟨valueEq,postEq⟩:=Prod.mk.inj (returnRun.symm.trans exactRun)
 have bounded : pointer.toNat+size.toNat≤33806089496 := by
  have subEq:=BitVec.toNat_sub_of_le (BitVec.le_def.mpr ordered : pointer≤scratch)
  rw [subEq] at request
  omega
 have coverage:=allocationEnd_covers pointer size bounded
 refine ⟨PanSemResultExact.returned.inj (Option.some.inj valueEq),?_,coverage.1,within,coverage.2.2,?_,?_,?_,?_,?_⟩
 all_goals simp [pPost,qPost,postEq,assigned,ready,entered,emptyLocalsHOLFinite,setVarHOLFinite,setKvarHOLFinite,setGlobalHOLFinite]
#print axioms frame_memory_allocation_returned
end InitECandidate.Runtime
