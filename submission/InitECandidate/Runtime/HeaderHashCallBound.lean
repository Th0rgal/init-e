import InitECandidate.Runtime.HeaderHashRuntimeBound
import InitECandidate.Runtime.OriginalHeaderHashCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual installed header hash derives the encoded length from the real
 header writer before hashing; its caller supplies only the original header. -/
theorem header_hash_installed_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap length pointer pad output : BitVec 64) (DF : Nat) (body : ProgHOL 64)
 (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (atState : s.globals.lookup (ofString "keccak_st")=some (.val (.word pointer)))
 (atPad : s.globals.lookup (ofString "keccak_pad")=some (.val (.word pad)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0) (outputAligned : output.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (lookup : lookupCodeHOLFinite s.code.lookup (ofString "header_hash") [.val (.word header),.val (.word output)]=some (body,callee,shape))
 (budget : headerHashSourceCost+1≤s.clock) :
 RunBounded (callEntryStateHOLFinite s callee) body headerHashSourceCost := by
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "header_hash") _ _ body _ shape _ callee
  (by rw [code];exact originalRuntimeCode_headerHash_lookup) lookup
 subst same
 rw [code] at lookup
 have bindings:=callee_eq originalRuntimeCode_headerHash_lookup lookup
 apply header_hash_body_bounded (callEntryStateHOLFinite s callee) header heap length pointer pad output DF code fence cap heapFence
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact atHeap
 · exact atState
 · exact atPad
 · simp [callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact heapCap
 · exact aligned
 · exact outputAligned
 · exact headerBelow
 · exact atLength
 · exact small
 · change headerHashSourceCost≤s.clock-1;omega

/-- Actual handler-free header_hash call for any destination and outcome. -/
theorem evaluate_header_hash_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64))
 (header heap length pointer pad output : BitVec 64) (DF : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word header),.val (.word output)])
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (atState : s.globals.lookup (ofString "keccak_st")=some (.val (.word pointer)))
 (atPad : s.globals.lookup (ofString "keccak_pad")=some (.val (.word pad)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0) (outputAligned : output.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : headerHashSourceCost+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "header_hash") arguments) (headerHashSourceCost+1) := by
 apply RunBounded.call args budget
 intro body callee shape lookup
 exact header_hash_installed_body_bounded s header heap length pointer pad output DF body callee shape code fence cap heapFence
  atHeap atState atPad heapCap aligned outputAligned headerBelow atLength small lookup budget
#print axioms header_hash_installed_body_bounded
#print axioms evaluate_header_hash_call_bounded
end InitECandidate.Runtime
