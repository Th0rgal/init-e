import InitECandidate.Runtime.HeapDeclarationReturnedContract
import InitECandidate.Runtime.PtNewBlkGD
import InitECandidate.Runtime.FundingReturnedLocal
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.PanHandlerFreeCallControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- The actual returned transaction environment constructor supplies its 200-byte
extent and preserves every earlier word. Every allocation/zeroing fact comes
from the same original returned run, with no minimum fuel or room premise. -/
theorem te_new_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (pointer watched : BitVec 64) (value : ValueHOL 64)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word pointer)))
 (aligned : pointer.toNat%8=0) (capped : pointer.toNat≤33806089496)
 (code : s.code=originalRuntimeCode) (before : watched.toNat<pointer.toNat)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_te_new)=(some (.returned value),post)) :
 value=.val (.word pointer) ∧
 post.globals=s.globals.update (ofString "heap_ptr",.val (.word (allocationEnd pointer 200))) ∧
 pointer.toNat+200≤(allocationEnd pointer 200).toNat ∧(allocationEnd pointer 200).toNat%8=0 ∧
 (allocationEnd pointer 200).toNat≤33806089496 ∧post.memory watched=s.memory watched ∧
 post.memaddrs=s.memaddrs ∧post.code=s.code := by
 rw [teNew_eq] at run
 unfold newBlkBody at run
 obtain ⟨allocated,output,tailRun,postEq,memory,domain,endian,installed,globals,request,finish⟩:=
  heap_declaration_returned_contract s post (ofString "te") (.const 200) _ pointer 200 value
   (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) atHeap code run
 let ready:=setVarHOLFinite (ofString "te") (.val (.word pointer)) {allocated with locals:=s.locals}
 change evaluateHOLFiniteState ready (.seq (.call (some (none,none)) (ofString "memzero")
  [.var .local (ofString "te"),.const 200]) (.return (.var .local (ofString "te"))))=_ at tailRun
 have atMessage : ready.locals.lookup (ofString "te")=some (.val (.word pointer)) := by
  simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have readyCode : ready.code=originalRuntimeCode:=installed.trans code
 have sumBound:=allocationGuard_sum_bound pointer 200 capped request
 have coverage:=allocationEnd_covers pointer 200 sumBound
 have sizeNat : (200#64 : BitVec 64).toNat=200 := rfl
 have fullExtent : pointer.toNat+200≤33806089496 := by change pointer.toNat+200≤33806089496 at sumBound;exact sumBound
 obtain ⟨zeroed,zeroRun,returnRun⟩:=encode_header_seq_returned_of_no_return ready output _ _ value
  (fun v=>(evaluate_handlerFree_call_control ready _ _ _).2.2 v) tailRun
 have args : evalListHOLFinite ready (h:=fun a=>Classical.propDecidable (ready.memaddrs a))
  [.var .local (ofString "te"),.const 200]=some [.val (.word pointer),.val (.word (200#64))] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atMessage]
 obtain ⟨framed,locals⟩:=memzero_call_normal_memory ready zeroed _ pointer 200 watched args readyCode aligned
  (by change pointer.toNat+200≤33806089496;exact fullExtent) (Or.inl before) zeroRun
 have atZeroMessage : zeroed.locals.lookup (ofString "te")=some (.val (.word pointer)) := by rw [locals];exact atMessage
 have exactReturn : evaluateHOLFiniteState zeroed (.return (.var .local (ofString "te")))=
  (some (.returned (.val (.word pointer))),emptyLocalsHOLFinite zeroed) := by
  simp [evaluateHOLFiniteState_return,evalHOLExact,atZeroMessage,shapeOfHOLExact]
 have returned:=Prod.mk.inj (returnRun.symm.trans exactReturn)
 have valueEq : value=.val (.word pointer):=PanSemResultExact.returned.inj (Option.some.inj returned.1)
 have endpoint : output=emptyLocalsHOLFinite zeroed:=returned.2
 have zeroGlobals:=memzero_call_globals_frame [.var .local (ofString "te"),.const 200] ready readyCode
 rw [zeroRun] at zeroGlobals
 have metadata:=evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_te_new)
 have originalRun : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_te_new)=(some (.returned value),post) := by
  rw [teNew_eq];exact run
 rw [originalRun] at metadata
 refine ⟨valueEq,?_,?_,coverage.2.2,finish,?_,metadata.2.1,metadata.1⟩
 · rw [postEq,endpoint]
   change zeroed.globals=_
   rw [zeroGlobals]
   exact globals
 · exact coverage.1
 · rw [postEq,endpoint]
   change zeroed.memory watched=s.memory watched
   exact framed.trans (congrFun memory watched)
#print axioms te_new_returned_frame
end InitECandidate.Runtime
