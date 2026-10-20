import InitECandidate.Runtime.EncodeHeaderNormalAssignmentContext
import InitECandidate.Runtime.EncodeHeaderWriterBodyFrames
import InitECandidate.Runtime.RecDecompGD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual header byte-call normal outcome, including cursor result and the
caller-local restoration used by the following p increment. -/
theorem encode_header_bytes_assignment_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (source : ExpHOL 64) (dst length lo watched : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atP : s.locals.lookup (ofString "p")=some (.val (.word dst)))
 (run : evaluateHOLFiniteState s (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes")
  [.var .local (ofString "p"),source,.const length])=(none,post)) :
 ∃written : BitVec 64,dst.toNat+written.toNat≤DF+8 ∧
 post.locals=s.locals.update (ofString "w",.val (.word written)) ∧
 post.memory watched=s.memory watched ∧post.globals=s.globals := by
 obtain ⟨values,body,callee,shape,value,bodyPost,args,lookup,bodyRun,postEq⟩:=
  encode_header_normal_assignment_context s post _ _ _ run
 cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) source with
 | none=>simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atP,evaluated] at args
 | some input=>
  have actual : values=[.val (.word dst),input,.val (.word length)] := by
   simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atP,evaluated] at args
   exact args.symm
  subst values
  have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_encode_bytes") _ _ body _ shape _ callee
   (by rw [code];exact originalRuntimeCode_rlpEncodeBytes_lookup) lookup
  subst same
  rw [code] at lookup
  have bindings:=callee_eq originalRuntimeCode_rlpEncodeBytes_lookup lookup
  let entry:=callEntryStateHOLFinite s callee
  have framed:=encode_header_bytes_body_returned_frame entry bodyPost dst length lo watched DF value code fence cap aligned below dstLow dstHigh
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE])
   (by simp [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]) bodyRun
  obtain ⟨written,rfl,bounded⟩:=framed.1
  refine ⟨written,bounded,?_,?_,?_⟩
  · rw [postEq];rfl
  · rw [postEq];exact framed.2.1
  · rw [postEq];exact framed.2.2
#print axioms encode_header_bytes_assignment_frame
end InitECandidate.Runtime
