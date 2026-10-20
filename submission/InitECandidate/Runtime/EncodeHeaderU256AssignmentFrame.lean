import InitECandidate.Runtime.EncodeHeaderNormalAssignmentContext
import InitECandidate.Runtime.EncodeHeaderRlpPutU256Returned
import InitECandidate.Runtime.RecDecompGD
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
theorem encode_header_u256_assignment_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (inputExp : ExpHOL 64) (dst heap lo watched : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atP : s.locals.lookup (ofString "p")=some (.val (.word dst)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (run : evaluateHOLFiniteState s (.call (some (some (.local,ofString "w"),none)) (ofString "rlp_put_u256")
  [.var .local (ofString "p"),inputExp])=(none,post)) :
 ∃written : BitVec 64,dst.toNat+written.toNat≤DF+8 ∧
 post.locals=s.locals.update (ofString "w",.val (.word written)) ∧
 post.memory watched=s.memory watched ∧post.globals=s.globals := by
 obtain ⟨values,body,callee,shape,value,bodyPost,args,lookup,bodyRun,postEq⟩:=encode_header_normal_assignment_context s post _ _ _ run
 cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) inputExp with
 | none=>simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atP,evaluated] at args
 | some input=>
  have actual : values=[.val (.word dst),input] := by
   simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atP,evaluated] at args
   exact args.symm
  subst values
  have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "rlp_put_u256") _ _ body _ shape _ callee
   (by rw [code];exact originalRuntimeCode_rlpPutU256_lookup) lookup
  subst same
  rw [code] at lookup
  have bindings:=callee_eq originalRuntimeCode_rlpPutU256_lookup lookup
  let entry:=callEntryStateHOLFinite s callee
  have framed:=encode_header_rlp_put_u256_returned entry bodyPost dst heap lo watched DF value code fence cap heapCap heapFence aligned below loHeap dstLow dstHigh
   (by simp (config:={decide:=true}) [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]) atHeap bodyRun
  obtain ⟨written,rfl,bounded⟩:=framed.1
  have globalsKept : bodyPost.globals=s.globals := by
   apply HolFiniteMapExact.ext
   funext key
   by_cases sameKey : key=ofString "heap_ptr"
   · subst sameKey
     exact framed.2.2.1.trans atHeap.symm
   · exact framed.2.2.2 key sameKey
  refine ⟨written,bounded,?_,?_,?_⟩
  · rw [postEq];rfl
  · rw [postEq];exact framed.2.1
  · rw [postEq];exact globalsKept
#print axioms encode_header_u256_assignment_frame
end InitECandidate.Runtime
