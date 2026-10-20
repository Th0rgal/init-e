import InitECandidate.Runtime.BlockRlpLengthRuntimeBound
import InitECandidate.Runtime.OriginalBlockRlpLengthCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The original installed block length body, with its real header record and
 the concrete extra-data length cell supplied by header construction. -/
theorem block_rlp_length_installed_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header payload heap length : BitVec 64) (DF : Nat) (body : ProgHOL 64)
 (callee : HolFiniteMapExact MlS (ValueHOL 64)) (shape : ShapeHOL)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (lookup : lookupCodeHOLFinite s.code.lookup (ofString "block_rlp_length") [.val (.word header),.val (.word payload)]=some (body,callee,shape))
 (budget : blockRlpLengthSourceCost+1≤s.clock) :
 RunBounded (callEntryStateHOLFinite s callee) body blockRlpLengthSourceCost := by
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "block_rlp_length") _ _ body _ shape _ callee
  (by rw [code];exact originalRuntimeCode_blockRlpLength_lookup) lookup
 subst same
 rw [code] at lookup
 have bindings:=callee_eq originalRuntimeCode_blockRlpLength_lookup lookup
 apply block_rlp_length_body_bounded (callEntryStateHOLFinite s callee) header heap length DF code fence cap heapFence
 · simp (config:={decide:=true}) [callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
 · exact atHeap
 · exact heapCap
 · exact aligned
 · exact headerBelow
 · exact atLength
 · exact small
 · change blockRlpLengthSourceCost≤s.clock-1;omega

/-- Actual handler-free block length call, for any destination and outcome. -/
theorem evaluate_block_rlp_length_call_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (destination : Option (VarKind×MlS)) (arguments : List (ExpHOL 64))
 (header payload heap length : BitVec 64) (DF : Nat)
 (args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) arguments=some [.val (.word header),.val (.word payload)])
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : blockRlpLengthSourceCost+1≤s.clock) :
 RunBounded s (.call (some (destination,none)) (ofString "block_rlp_length") arguments) (blockRlpLengthSourceCost+1) := by
 apply RunBounded.call args budget
 intro body callee shape lookup
 exact block_rlp_length_installed_body_bounded s header payload heap length DF body callee shape code fence cap heapFence
  atHeap heapCap aligned headerBelow atLength small lookup budget
#print axioms block_rlp_length_installed_body_bounded
#print axioms evaluate_block_rlp_length_call_bounded
end InitECandidate.Runtime
