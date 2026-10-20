import InitECandidate.Runtime.OriginalEncodeHeaderCode
import InitECandidate.Runtime.EncodeHeaderRuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual installed header body at any real lookup uses its concrete
caller heap and original retained header length cell. -/
theorem encode_header_installed_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap length : BitVec 64) (DF : Nat) (body : ProgHOL 64)
 (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (lookup : lookupCodeHOLFinite s.code.lookup (ofString "encode_header") [.val (.word header)]=some (body,callee,shape))
 (budget : encodeHeaderSourceCost+1≤s.clock) :
 RunBounded (callEntryStateHOLFinite s callee) body encodeHeaderSourceCost := by
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "encode_header") _ _ body _ shape _ callee
  (by rw [code];exact originalRuntimeCode_encodeHeader_lookup) lookup
 subst same
 rw [code] at lookup
 have bindings:=callee_eq originalRuntimeCode_encodeHeader_lookup lookup
 apply encode_header_body_bounded (callEntryStateHOLFinite s callee) header heap length DF code fence cap heapFence
 · simp [callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact atHeap
 · exact heapCap
 · exact aligned
 · exact headerBelow
 · exact atLength
 · exact small
 · change encodeHeaderSourceCost≤s.clock-1;omega

/-- Actual handler-free encode_header call, for every destination and outcome. -/
theorem evaluate_encode_header_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64))
 (header heap length : BitVec 64) (DF : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word header)])
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : encodeHeaderSourceCost+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "encode_header") arguments) (encodeHeaderSourceCost+1) := by
 apply RunBounded.call args budget
 intro body callee shape lookup
 exact encode_header_installed_body_bounded s header heap length DF body callee shape code fence cap heapFence
  atHeap heapCap aligned headerBelow atLength small lookup budget
#print axioms encode_header_installed_body_bounded
#print axioms evaluate_encode_header_call_bounded
end InitECandidate.Runtime
