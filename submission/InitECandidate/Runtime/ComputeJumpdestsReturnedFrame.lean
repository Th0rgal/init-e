import InitECandidate.Runtime.ComputeJumpdestsLoopFrame
import InitECandidate.Runtime.ComputeJumpdestsGlobalsFrame
import InitECandidate.Runtime.ScratchAllocationReturnedAnyClock
import InitECandidate.Runtime.ScratchAllocationAligned
import InitECandidate.Runtime.OriginalScratchAllocationCode
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
import InitECandidate.Runtime.FundingAllocationReturnedContext
import InitECandidate.Runtime.FundingReturnedLocal
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.MemzeroNormalFrame
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.WhileTerminalControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem eval_compute_jumpdests_size {F : Type} (s : PanSemStateFiniteExact 64 F) (length : BitVec 64)
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length))) :
 @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) computeJumpdestsSizeExpression=
 some (.val (.word (computeJumpdestsBitmapSize length))) := by
 simp [computeJumpdestsSizeExpression,computeJumpdestsBitmapSize,evalHOLExact,evalListHOLExact,atLength,
  wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,wordShiftHOL]

/-- Complete actual returned bitmap construction frames every word at or
above the scratch frontier at entry. Allocation success/space, byte access,
zeroing success and scan iterations are all derived from this same original
returned execution; no runtime or callee-frame callback is supplied. -/
theorem compute_jumpdests_returned_upper_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (scratch frame length watched : BitVec 64) (value : ValueHOL 64)
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (ordered : frame≤scratch) (cap : scratch.toNat≤33806089496) (small : length.toNat≤134217712)
 (code : s.code=originalRuntimeCode) (above : scratch.toNat≤watched.toNat)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_compute_jumpdests)=(some (.returned value),post)) :
 value=.val (.word (scratchAllocationEnd scratch (computeJumpdestsBitmapSize length))) ∧
 post.memory watched=s.memory watched ∧
 post.globals=s.globals.update (ofString "scratch_ptr",.val (.word (scratchAllocationEnd scratch (computeJumpdestsBitmapSize length)))) ∧
 frame.toNat≤(scratchAllocationEnd scratch (computeJumpdestsBitmapSize length)).toNat ∧
 (scratchAllocationEnd scratch (computeJumpdestsBitmapSize length)).toNat+(computeJumpdestsBitmapSize length).toNat≤scratch.toNat := by
 classical
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (computeJumpdestsAt 0)=_ at run
 rw [source_compute_jumpdests_entry] at run
 let size:=computeJumpdestsBitmapSize length
 let bitmap:=scratchAllocationEnd scratch size
 have arguments : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [computeJumpdestsSizeExpression]=
  some [.val (.word size)] := by
  have sizeEval:=eval_compute_jumpdests_size s length atLength
  simp only [evalListHOLFinite,evalListHOLExact]
  rw [sizeEval]
 have installed : s.code.lookup (ofString "scratch_alloc")=
  some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_scratch_alloc,.one) := by
  rw [code];exact originalRuntimeCode_scratchAllocation_lookup
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
 have lookup:=pan_single_word_lookup s.code.lookup (ofString "scratch_alloc") (ofString "n")
  (sourceFunctionBody Guest.guestFn_scratch_alloc) size installed
 obtain ⟨allocated,allocationPost,output,allocationRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post (ofString "bm") (ofString "scratch_alloc") .one .one _ _ _ _ callee value
   arguments lookup run
 let entry:=callEntryStateHOLFinite s callee
 have nEntry : entry.locals.lookup (ofString "n")=some (.val (.word size)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨allocatedEq,atNext,lower,extent,memory,domain,endian,installedKept⟩:=scratch_allocation_returned_progress_any_clock entry allocationPost
  scratch size frame allocated scratchGlobal nEntry frameGlobal ordered code allocationRun
 have allocationGlobals:=scratch_allocation_returned_globals_any_clock entry allocationPost scratch size frame allocated
  scratchGlobal nEntry frameGlobal ordered code allocationRun
 subst allocated
 change bitmap.toNat+size.toNat≤scratch.toNat at extent
 let ready:=setVarHOLFinite (ofString "bm") (.val (.word bitmap)) {allocationPost with locals:=s.locals}
 change evaluateHOLFiniteState ready (computeJumpdestsAt 1)=_ at tailRun
 have atBitmap : ready.locals.lookup (ofString "bm")=some (.val (.word bitmap)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have atN : ready.locals.lookup (ofString "n")=some (.val (.word length)) := by
  simpa (config:={decide:=true}) [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atLength
 rw [source_compute_jumpdests_zero] at tailRun
 obtain ⟨afterZero,zeroRun,afterZeroRun⟩:=encode_header_seq_returned_of_no_return ready output _ _ value
  (fun v=>(evaluate_handlerFree_call_control ready _ _ _).2.2 v) tailRun
 have zeroArgs : evalListHOLFinite ready (h:=fun a=>Classical.propDecidable (ready.memaddrs a))
  [.var .local (ofString "bm"),computeJumpdestsSizeExpression]=some [.val (.word bitmap),.val (.word size)] := by
  have evaluated:=eval_compute_jumpdests_size ready length atN
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atBitmap,evaluated,size]
 have readyCode : ready.code=originalRuntimeCode := installedKept.trans code
 have bitmapAligned : bitmap.toNat%8=0:=scratchAllocationEnd_mask_aligned scratch size
 have sizeBound : bitmap.toNat+size.toNat≤33806089496:=by omega
 obtain ⟨zeroFrame,zeroLocals⟩:=memzero_call_normal_memory ready afterZero _ bitmap size watched zeroArgs readyCode bitmapAligned sizeBound
  (Or.inr (by omega)) zeroRun
 have bmZero : afterZero.locals.lookup (ofString "bm")=some (.val (.word bitmap)) := by rw [zeroLocals];exact atBitmap
 have nZero : afterZero.locals.lookup (ofString "n")=some (.val (.word length)) := by rw [zeroLocals];exact atN
 have afterZeroOriginal:=afterZeroRun
 rw [source_compute_jumpdests_pc] at afterZeroRun
 obtain ⟨pcValue,loopOutput,pcEval,loopRun,pcPost⟩:=funding_declaration_returned_context afterZeroRun
 have pcEq : pcValue=.val (.word (0#64)) := by simpa [evalHOLExact] using pcEval.symm
 subst pcValue
 let loopEntry:=setVarHOLFinite (ofString "pc") (.val (.word 0)) afterZero
 change evaluateHOLFiniteState loopEntry (computeJumpdestsAt 3)=_ at loopRun
 rw [source_compute_jumpdests_loop] at loopRun
 obtain ⟨afterLoop,loopNormal,returnRun⟩:=encode_header_seq_returned_of_no_return loopEntry loopOutput _ _ value
  (evaluate_while_terminal_control computeJumpdestsCondition computeJumpdestsLoopBody
   (fun current v=>evaluate_noDirectReturn _ (by decide_cbv) current v) loopEntry).2.2 loopRun
 have loopBitmap : loopEntry.locals.lookup (ofString "bm")=some (.val (.word bitmap)) := by
  simpa (config:={decide:=true}) [loopEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using bmZero
 have loopLength : loopEntry.locals.lookup (ofString "n")=some (.val (.word length)) := by
  simpa (config:={decide:=true}) [loopEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using nZero
 have loopFrame:=compute_jumpdests_loop_upper_frame loopEntry afterLoop bitmap length watched scratch.toNat loopBitmap loopLength small extent cap above loopNormal
 have bmKept:=evaluate_avoidsLocal_flowing (ofString "bm") (.while computeJumpdestsCondition computeJumpdestsLoopBody)
  (by decide_cbv) loopEntry (by rw [loopNormal];exact Or.inl rfl)
 rw [loopNormal] at bmKept
 have bmAfter : afterLoop.locals.lookup (ofString "bm")=some (.val (.word bitmap)):=bmKept.trans loopBitmap
 have exactReturn : evaluateHOLFiniteState afterLoop (computeJumpdestsAt 4)=
  (some (.returned (.val (.word bitmap))),emptyLocalsHOLFinite afterLoop) := by
  change evaluateHOLFiniteState afterLoop (.return (.var .local (ofString "bm")))=_
  simp [evaluateHOLFiniteState_return,evalHOLExact,bmAfter,shapeOfHOLExact]
 have valueEq:=PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (returnRun.symm.trans exactReturn)).1)
 have suffixGlobals:=compute_jumpdests_suffix_globals_frame ready readyCode
 change (evaluateHOLFiniteState ready (computeJumpdestsAt 1)).2.globals=ready.globals at suffixGlobals
 have tailOriginal : evaluateHOLFiniteState ready (computeJumpdestsAt 1)=(some (.returned value),output) := by
  rw [source_compute_jumpdests_zero]
  exact evaluate_seq_none zeroRun afterZeroOriginal
 rw [tailOriginal] at suffixGlobals
 have endpointGlobals : post.globals=s.globals.update (ofString "scratch_ptr",.val (.word bitmap)) := by
  rw [postEq]
  exact suffixGlobals.trans allocationGlobals
 refine ⟨valueEq,?_,endpointGlobals,lower,extent⟩
 have returnFrame:=evaluate_readOnly_memory (computeJumpdestsAt 4) (by decide_cbv) afterLoop
 rw [returnRun] at returnFrame
 have readyMemory : ready.memory=s.memory:=memory
 rw [postEq,pcPost]
 change loopOutput.memory watched=s.memory watched
 rw [returnFrame,loopFrame]
 exact zeroFrame.trans (congrFun readyMemory watched)
#print axioms eval_compute_jumpdests_size
#print axioms compute_jumpdests_returned_upper_frame
end InitECandidate.Runtime
