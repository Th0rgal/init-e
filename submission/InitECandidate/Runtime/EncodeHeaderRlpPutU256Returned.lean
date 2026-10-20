import InitECandidate.Runtime.EncodeHeaderPutU256MinReturned
import InitECandidate.Runtime.HeapMarkCall
import InitECandidate.Runtime.AllocationDeclarationReturned
import InitECandidate.Runtime.PanDecCallReturnedNonzeroClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual original RLP minimal-uint writer cursor and old-memory frame,
without assuming the later transaction journal arena exists. -/
theorem encode_header_rlp_put_u256_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (dst heap lo watched : BitVec 64) (DF : Nat) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_rlp_put_u256)=(some (.returned value),post)) :
 WRet DF dst value ∧post.memory watched=s.memory watched ∧
 post.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) ∧
 (∀key,key≠ofString "heap_ptr"→post.globals.lookup key=s.globals.lookup key) := by
 rw [sourceFunctionBody_eq_structural] at run
 change evaluateHOLFiniteState s (rlpPutU256At 0)=(some (.returned value),post) at run
 rw [source_rlp_put_u256_prefix.1] at run
 have ticks:=evaluate_decCall_returned_nonzero_clock s post _ _ _ _ _ value run
 obtain ⟨marked,_,_,markMemory,markGlobals,markLocals,markCode,markDomain,_,declaration⟩:=evaluate_heapMark_call_and_declaration s heap code atHeap ticks
 rw [declaration (ofString "mark") (rlpPutU256At 1)] at run
 let entered:=setVarHOLFinite (ofString "mark") (.val (.word heap)) marked
 cases restRun : evaluateHOLFiniteState entered (rlpPutU256At 1) with
 | mk result output=>
  change (let held:=evaluateHOLFiniteState entered (rlpPutU256At 1);
   (held.1,{held.2 with locals:=HolFiniteMapExact.resVarEq held.2.locals (ofString "mark",s.locals.lookup (ofString "mark"))}))=
    (some (PanSemResultExact.returned value),post) at run
  rw [restRun] at run
  have control := (Prod.mk.inj run).1
  change result=some (.returned value) at control
  subst result
  have postMemory : post.memory=output.memory := by rw [←(Prod.mk.inj run).2]
  have postGlobals : post.globals=output.globals := by rw [←(Prod.mk.inj run).2]
  have enteredCode : entered.code=originalRuntimeCode := markCode.trans code
  have enteredHeap : entered.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)) := by
   change marked.globals.lookup _=_
   rw [markGlobals];exact atHeap
  rw [source_rlp_put_u256_prefix.2.1] at restRun
  obtain ⟨allocated,inner,innerRun,allocatedLocals,allocatedMemory,allocatedCode,allocatedDomain,allocatedGlobals,_,_,_,outputMemory,outputGlobals,_⟩:=
   allocation_declaration_returned entered output (ofString "tmp") (.const 32) (rlpPutU256At 2) heap 32 value
    (by rw [evalListHOLFinite_eq_toExact];rfl) enteredCode enteredHeap heapCap restRun
  have allocatedFence : Fence allocated.memaddrs DF := by
   rw [allocatedDomain]
   change Fence marked.memaddrs DF
   rw [markDomain];exact fence
  have allocatedDst : allocated.locals.lookup (ofString "dst")=some (.val (.word dst)) := by
   rw [allocatedLocals]
   simp (config:={decide:=true}) [entered,setVarHOLFinite,markLocals,HolFiniteMapExact.lookup_update,FUPDATE,atDst]
  have allocatedMark : allocated.locals.lookup (ofString "mark")=some (.val (.word heap)) := by
   rw [allocatedLocals]
   simp (config:={decide:=true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have allocatedTmp : allocated.locals.lookup (ofString "tmp")=some (.val (.word heap)) := by
   rw [allocatedLocals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have allocatedHeap : allocated.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 32))) := by
   rw [allocatedGlobals]
   simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have finished:=encode_header_put_u256_min_returned allocated inner dst heap heap (allocationEnd heap 32) lo watched DF value
   (allocatedCode.trans enteredCode) allocatedFence cap aligned below dstLow dstHigh loHeap (by omega)
   allocatedDst allocatedTmp allocatedMark allocatedHeap innerRun
  refine ⟨finished.1,?_,?_,?_⟩
  · rw [postMemory,outputMemory,finished.2.1,allocatedMemory]
    change marked.memory watched=s.memory watched
    rw [markMemory]
  · rw [postGlobals,outputGlobals,finished.2.2]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key different
    rw [postGlobals,outputGlobals,finished.2.2]
    simp only [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    rw [allocatedGlobals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    change marked.globals.lookup key=s.globals.lookup key
    rw [markGlobals]
#print axioms encode_header_rlp_put_u256_returned
end InitECandidate.Runtime
