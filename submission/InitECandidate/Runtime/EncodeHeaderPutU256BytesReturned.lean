import InitECandidate.Runtime.EncodeHeaderReturnedDeclarationContext
import InitECandidate.Runtime.RlpPutU256EncodeTailBound
import InitECandidate.Runtime.HeapReleaseCall
import InitECandidate.Runtime.PanDiscardCallNormalResult
import InitECandidate.Runtime.AllocationFramedGlobals
import InitECandidate.Runtime.GlobalKeep
import InitECandidate.Runtime.HtabFindSlotReturned
import InitECandidate.Runtime.StateInitFinalTailReturnedMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual minimal writer suffix needs no journal arena: only the byte
 encoder writes memory, and the real release restores the supplied mark. -/
theorem encode_header_put_u256_bytes_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (dst tmp length mark current lo watched : BitVec 64) (DF : Nat) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atTmp : s.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
 (atLength : s.locals.lookup (ofString "n")=some (.val (.word length)))
 (atMark : s.locals.lookup (ofString "mark")=some (.val (.word mark)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word current)))
 (run : evaluateHOLFiniteState s (rlpPutU256At 3)=(some (.returned value),post)) :
 WRet DF dst value ∧post.memory watched=s.memory watched ∧
 post.globals=(setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mark)) s).globals := by
 rw [source_rlp_put_u256_encode] at run
 obtain ⟨values,body,callee,shape,returned,bodyPost,ready,output,args,lookup,bodyRun,locals,memory,globals,clock,domain,endian,installed,tailRun,postEq⟩:=
  encode_header_returned_declaration_context s post _ _ _ _ _ value run
 have arguments : values=[.val (.word dst),.val (.word tmp),.val (.word length)] := by
  simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atDst,atTmp,atLength] at args
  exact args.symm
 subst values
 have actualLookup:=pan_three_word_lookup s.code.lookup (ofString "rlp_encode_bytes") (ofString "dst") (ofString "src") (ofString "n")
  (sourceFunctionBody Guest.guestFn_rlp_encode_bytes) dst tmp length (by decide) (by decide) (by decide) (by rw [code];exact originalRuntimeCode_rlpEncodeBytes_lookup)
 rw [actualLookup] at lookup
 obtain ⟨rfl,rfl,rfl⟩:=Option.some.inj lookup |>.symm
 let entry:=callEntryStateHOLFinite s (((HolFiniteMapExact.empty.update (ofString "dst",.val (.word dst))).update
  (ofString "src",.val (.word tmp))).update (ofString "n",.val (.word length)))
 have spec:=encodeBytes_win (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=watched) fence cap lo aligned below dst length dstLow (by omega)
 have dom : DomD s.memaddrs s.be entry := ⟨(by intro a ha;have h:=fence a ha;omega),rfl,rfl⟩
 have facts:=spec F entry code dom trivial (by intro name impossible;exact impossible.elim) entry.globals rfl
  ⟨(by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]),
   (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])⟩
 have bytesFrame : bodyPost.memory watched=s.memory watched := by
  have kept:=facts.1
  rw [bodyRun] at kept
  exact kept
 obtain ⟨_,_,cursor⟩:=facts.2.2.2.1 returned (by rw [bodyRun])
 obtain ⟨written,valueEq,bound⟩:=cursor
 subst valueEq
 have bytesGlobals:=evaluate_keepsGA goodGA goodGA_bodies (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)
  (keepsGA_of_installed originalRuntimeCode_rlpEncodeBytes_lookup (by decide)) entry code
 rw [bodyRun] at bytesGlobals
 let resumed:=setVarHOLFinite (ofString "w") (.val (.word written)) ready
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_encode_bytes)
 rw [bodyRun] at metadata
 have resumeCode : resumed.code=originalRuntimeCode := installed.trans (metadata.1.trans code)
 have releaseArgs : evalListHOLFinite resumed (h:=fun a=>Classical.propDecidable (resumed.memaddrs a)) [.var .local (ofString "mark")]=some [.val (.word mark)] := by
  have boundMark : resumed.locals.lookup (ofString "mark")=some (.val (.word mark)) := by
   change (ready.locals.update (ofString "w",.val (.word written))).lookup (ofString "mark")=_
   rw [lookup_update_ne' _ _ (by decide),locals]
   exact atMark
  rw [evalListHOLFinite_eq_toExact]
  simp [evalListHOLExact,evalHOLExact,boundMark]
 have heap : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word current)) := by
  change ready.globals.lookup _=_
  rw [globals,bytesGlobals]
  exact atHeap
 obtain ⟨released,releaseRun,returnRun⟩:=seq_returned_of_nonreturning_first
  (fun v=>discard_call_not_returned resumed (ofString "heap_release") [.var .local (ofString "mark")] v) tailRun
 have releaseLookup:=pan_single_word_lookup resumed.code.lookup (ofString "heap_release") (ofString "m")
  (sourceFunctionBody Guest.guestFn_heap_release) mark (by rw [resumeCode];exact originalRuntimeCode_heap_release_lookup)
 have ticks : resumed.clock≠0 := by
  intro zero
  rw [evaluateHOLFiniteState_call,releaseArgs] at releaseRun
  simp only at releaseRun
  rw [releaseLookup] at releaseRun
  simp [zero] at releaseRun
 obtain ⟨actual,actualRun,_,releaseMemory,releaseGlobals,releaseLocals,_,_,_⟩:=evaluate_heapRelease_call resumed
  (.var .local (ofString "mark")) mark current resumeCode releaseArgs heap ticks
 rw [actualRun] at releaseRun
 cases (Prod.mk.inj releaseRun).2
 have atWritten : released.locals.lookup (ofString "w")=some (.val (.word written)) := by
  rw [releaseLocals]
  simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 have finalValue:=return_local_word released output (ofString "w") written value atWritten returnRun
 have finalMemory:=state_init_return_memory_all released (.var .local (ofString "w"))
 have finalGlobals : output.globals=released.globals := by
  have terminal : evaluateHOLFiniteState released (.return (.var .local (ofString "w")))=(some (.returned (.val (.word written))),emptyLocalsHOLFinite released) := by
   simp [evaluateHOLFiniteState_return,evalHOLExact,atWritten,shapeOfHOLExact]
  have equal := returnRun
  rw [terminal] at equal
  exact congrArg (fun st=>st.globals) (Prod.mk.inj equal).2.symm
 rw [returnRun] at finalMemory
 refine ⟨⟨written,finalValue,bound⟩,?_,?_⟩
 · rw [postEq]
   change output.memory watched=s.memory watched
   rw [finalMemory,releaseMemory]
   change ready.memory watched=s.memory watched
   rw [memory]
   exact bytesFrame
 · rw [postEq]
   change output.globals=_
   rw [finalGlobals,releaseGlobals]
   change ready.globals.update (ofString "heap_ptr",.val (.word mark))=s.globals.update (ofString "heap_ptr",.val (.word mark))
   rw [globals,bytesGlobals]
   rfl
#print axioms encode_header_put_u256_bytes_returned
end InitECandidate.Runtime
