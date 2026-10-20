import InitECandidate.Runtime.FrameNewScratchCallees
import InitECandidate.Runtime.OriginalComputeJumpdestsCode
import InitECandidate.Runtime.VmFn_lst_new_scratch
import InitECandidate.Runtime.OriginalHashNewScratchCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

theorem original_frame_new_scratch_callee_lookup (kind : FrameNewScratchCallee) :
 originalRuntimeCode.lookup kind.function=some ([(kind.firstName,.one),(kind.secondName,.one)],kind.body,.one) := by
 cases kind with
 | bitmap code length=>exact originalRuntimeCode_computeJumpdests_lookup
 | logs=>exact vmLookup_lst_new_scratch
 | destruction=>exact originalRuntimeCode_htabNewScratch_lookup

/-- The actual original frame_new scratch declaration preserves a protected
old word and exposes its real typed returned pointer/new frontier. All three
named callees are closed above; no callee-frame premise is accepted here. -/
theorem frame_new_scratch_declaration_returned {F : Type} (kind : FrameNewScratchCallee)
 (s post : PanSemStateFiniteExact 64 F) (name : MlS) (firstArgument secondArgument : ExpHOL 64) (tail : ProgHOL 64)
 (scratch frame watched : BitVec 64) (value : ValueHOL 64)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [firstArgument,secondArgument]=
  some [.val (.word kind.firstWord),.val (.word kind.secondWord)])
 (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
 (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
 (ordered : frame≤scratch) (cap : scratch.toNat≤33806089496) (above : scratch.toNat≤watched.toNat)
 (code : s.code=originalRuntimeCode) (codeBound : kind.codeBound)
 (run : evaluateHOLFiniteState s (.decCall name .one kind.function [firstArgument,secondArgument] tail)=(some (.returned value),post)) :
 ∃pointer frontier : BitVec 64,∃bodyPost output : PanSemStateFiniteExact 64 F,
 evaluateHOLFiniteState (setVarHOLFinite name (.val (.word pointer)) {bodyPost with locals:=s.locals}) tail=(some (.returned value),output) ∧
 post={output with locals:=HolFiniteMapExact.resVarEq output.locals (name,s.locals.lookup name)} ∧
 bodyPost.globals=s.globals.update (ofString "scratch_ptr",.val (.word frontier)) ∧
 frame.toNat≤frontier.toNat ∧frontier.toNat≤pointer.toNat ∧pointer.toNat≤scratch.toNat ∧
 bodyPost.memory watched=s.memory watched ∧bodyPost.memaddrs=s.memaddrs ∧bodyPost.be=s.be ∧bodyPost.code=s.code ∧
 (∀other : BitVec 64,scratch.toNat≤other.toNat → bodyPost.memory other=s.memory other) := by
 have namesDifferent : kind.firstName≠kind.secondName := by cases kind <;>simp only [FrameNewScratchCallee.firstName,FrameNewScratchCallee.secondName] <;>decide
 have installed : s.code.lookup kind.function=some ([(kind.firstName,.one),(kind.secondName,.one)],kind.body,.one) := by
  rw [code];exact original_frame_new_scratch_callee_lookup kind
 let callee : HolFiniteMapExact MlS (ValueHOL 64):=
  (HolFiniteMapExact.empty.update (kind.firstName,.val (.word kind.firstWord))).update (kind.secondName,.val (.word kind.secondWord))
 have lookup:=pan_two_word_lookup s.code.lookup kind.function kind.firstName kind.secondName kind.body kind.firstWord kind.secondWord namesDifferent installed
 obtain ⟨allocated,bodyPost,output,bodyRun,checked,tailRun,postEq⟩:=
  evaluate_decCall_checked_returned_exact_scope s post name kind.function .one .one _ _ _ _ callee value args lookup run
 let entry:=callEntryStateHOLFinite s callee
 have firstLocal : entry.locals.lookup kind.firstName=some (.val (.word kind.firstWord)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,namesDifferent,Ne.symm namesDifferent]
 have secondLocal : entry.locals.lookup kind.secondName=some (.val (.word kind.secondWord)) := by
  simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 obtain ⟨pointer,frontier,returned,globals,lower,beforePointer,beforeScratch,memory,domain,endian,installedKept⟩:=
  frame_new_actual_scratch_callee_returned kind entry bodyPost scratch frame watched allocated firstLocal secondLocal scratchGlobal frameGlobal ordered cap above code codeBound bodyRun
 subst allocated
 have allMemory : ∀other : BitVec 64,scratch.toNat≤other.toNat → bodyPost.memory other=s.memory other := by
  intro other aboveOther
  obtain ⟨p,q,result,globalEq,lowerEq,pointerEq,scratchEq,wordFrame,rest⟩:=
   frame_new_actual_scratch_callee_returned kind entry bodyPost scratch frame other (.val (.word pointer)) firstLocal secondLocal scratchGlobal frameGlobal ordered cap aboveOther code codeBound bodyRun
  exact wordFrame
 exact ⟨pointer,frontier,bodyPost,output,tailRun,postEq,globals,lower,beforePointer,beforeScratch,memory,domain,endian,installedKept,allMemory⟩
#print axioms original_frame_new_scratch_callee_lookup
#print axioms frame_new_scratch_declaration_returned
end InitECandidate.Runtime
