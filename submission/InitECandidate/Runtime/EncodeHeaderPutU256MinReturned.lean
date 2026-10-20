import InitECandidate.Runtime.EncodeHeaderPutU256BytesReturned
import InitECandidate.Runtime.U256ToBeMinReturnedCeiling
import InitECandidate.Runtime.RlpPutU256RuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual minimal-uint writer after temporary allocation: its scratch writes
are above lo, and the real remaining byte/release tail preserves the old cell. -/
theorem encode_header_put_u256_min_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (dst tmp mark current lo watched : BitVec 64) (DF : Nat) (value : ValueHOL 64)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (tmpLow : lo.toNat≤tmp.toNat) (tmpHigh : tmp.toNat≤DF+8)
 (atDst : s.locals.lookup (ofString "dst")=some (.val (.word dst)))
 (atTmp : s.locals.lookup (ofString "tmp")=some (.val (.word tmp)))
 (atMark : s.locals.lookup (ofString "mark")=some (.val (.word mark)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word current)))
 (run : evaluateHOLFiniteState s (rlpPutU256At 2)=(some (.returned value),post)) :
 WRet DF dst value ∧post.memory watched=s.memory watched ∧
 post.globals=(setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mark)) s).globals := by
 rw [source_rlp_put_u256_prefix.2.2] at run
 obtain ⟨values,body,callee,shape,returned,bodyPost,ready,output,args,lookup,bodyRun,locals,memory,globals,clock,domain,endian,installed,tailRun,postEq⟩:=
  encode_header_returned_declaration_context s post _ _ _ _ _ value run
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "u256_to_be_min") _ _ body _ shape values callee
  (by rw [code];exact originalRuntimeCode_u256ToBeMin_lookup) lookup
 subst same
 have atOut : (callEntryStateHOLFinite s callee).locals.lookup (ofString "out")=some (.val (.word tmp)) := by
  cases held : s.locals.lookup (ofString "v") with
  | none=>simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,held] at args
  | some input=>
   have actual : values=[input,.val (.word tmp)] := by
    simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,held,atTmp] at args
    exact args.symm
   subst values
   rw [code] at lookup
   have bindings:=callee_eq originalRuntimeCode_u256ToBeMin_lookup lookup
   simp [callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
 let entry:=callEntryStateHOLFinite s callee
 have spec:=toBeMin_win (D:=s.memaddrs) (B:=s.be) (A:=fun _=>True) (w:=watched) fence cap lo aligned below tmp tmpLow tmpHigh
 have dom : DomD s.memaddrs s.be entry := ⟨(by intro a ha;have h:=fence a ha;omega),rfl,rfl⟩
 have facts:=spec F entry code dom trivial (by intro name impossible;exact impossible.elim) entry.globals rfl atOut
 have minFrame : bodyPost.memory watched=s.memory watched := by
  have frame:=facts.1
  rw [bodyRun] at frame
  exact frame
 have minGlobals:=evaluate_keepsGA goodGA goodGA_bodies (sourceFunctionBody Guest.guestFn_u256_to_be_min)
  (keepsGA_of_installed originalRuntimeCode_u256ToBeMin_lookup (by decide)) entry code
 rw [bodyRun] at minGlobals
 obtain ⟨length,rfl,_⟩:=u256_to_be_min_returned_ceiling entry bodyPost returned code bodyRun
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_u256_to_be_min)
 rw [bodyRun] at metadata
 let resumed:=setVarHOLFinite (ofString "n") (.val (.word length)) ready
 have resumeCode : resumed.code=originalRuntimeCode := installed.trans (metadata.1.trans code)
 have resumeDomain : resumed.memaddrs=s.memaddrs := domain.trans metadata.2.1
 have resumedFence : Fence resumed.memaddrs DF := by rw [resumeDomain];exact fence
 have dstKept : resumed.locals.lookup (ofString "dst")=some (.val (.word dst)) := by
  simp (config:={decide:=true}) [resumed,setVarHOLFinite,locals,HolFiniteMapExact.lookup_update,FUPDATE,atDst]
 have tmpKept : resumed.locals.lookup (ofString "tmp")=some (.val (.word tmp)) := by
  simp (config:={decide:=true}) [resumed,setVarHOLFinite,locals,HolFiniteMapExact.lookup_update,FUPDATE,atTmp]
 have markKept : resumed.locals.lookup (ofString "mark")=some (.val (.word mark)) := by
  simp (config:={decide:=true}) [resumed,setVarHOLFinite,locals,HolFiniteMapExact.lookup_update,FUPDATE,atMark]
 have heapKept : resumed.globals.lookup (ofString "heap_ptr")=some (.val (.word current)) := by
  change ready.globals.lookup _=_
  rw [globals,minGlobals]
  exact atHeap
 have result:=encode_header_put_u256_bytes_returned resumed output dst tmp length mark current lo watched DF value
  resumeCode resumedFence cap aligned below dstLow dstHigh dstKept tmpKept
  (by simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) markKept heapKept tailRun
 refine ⟨result.1,?_,?_⟩
 · rw [postEq]
   change output.memory watched=s.memory watched
   rw [result.2.1]
   change ready.memory watched=s.memory watched
   rw [memory]
   exact minFrame
 · rw [postEq]
   change output.globals=_
   rw [result.2.2]
   change ready.globals.update (ofString "heap_ptr",.val (.word mark))=s.globals.update (ofString "heap_ptr",.val (.word mark))
   rw [globals,minGlobals]
   rfl
#print axioms encode_header_put_u256_min_returned
end InitECandidate.Runtime
