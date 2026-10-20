import InitECandidate.Runtime.EncodeHeaderBytesAssignmentFrame
import InitECandidate.Runtime.EncodeHeaderWordAssignmentFrame
import InitECandidate.Runtime.EncodeHeaderU256AssignmentFrame
import InitECandidate.Runtime.RlpEncodeBytesFixedCallBound
import InitECandidate.Runtime.RlpWritersRuntimeBound
import InitECandidate.Runtime.RlpPutU256RuntimeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
inductive EncodeHeaderPrefixWriter where
 | bytes (length : BitVec 64)
 | word
 | u256

def encodeHeaderPrefixWriterCall (writer : EncodeHeaderPrefixWriter) (input : ExpHOL 64) : ProgHOL 64 :=
 match writer with
 | .bytes n=>.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_bytes") [.var .local (ofString "p"),input,.const n]
 | .word=>.call (some (some (.local,ofString "w"),none)) (ofString "rlp_encode_word") [.var .local (ofString "p"),input]
 | .u256=>.call (some (some (.local,ofString "w"),none)) (ofString "rlp_put_u256") [.var .local (ofString "p"),input]

/-- All actual writer forms in the variable-call prefix retain the watched
original header word. No initialized-journal predicate is used. -/
theorem encode_header_prefix_writer_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (writer : EncodeHeaderPrefixWriter) (input : ExpHOL 64) (dst heap lo watched : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62)
 (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (dstLow : lo.toNat≤dst.toNat) (dstHigh : dst.toNat≤DF+8)
 (atP : s.locals.lookup (ofString "p")=some (.val (.word dst)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (run : evaluateHOLFiniteState s (encodeHeaderPrefixWriterCall writer input)=(none,post)) :
 ∃written : BitVec 64,dst.toNat+written.toNat≤DF+8 ∧
 post.locals=s.locals.update (ofString "w",.val (.word written)) ∧
 post.memory watched=s.memory watched ∧post.globals=s.globals := by
 cases writer with
 | bytes n=>exact encode_header_bytes_assignment_frame s post input dst n lo watched DF code fence cap aligned below dstLow dstHigh atP run
 | word=>exact encode_header_word_assignment_frame s post input dst lo watched DF code fence cap aligned below dstLow dstHigh atP run
 | u256=>exact encode_header_u256_assignment_frame s post input dst heap lo watched DF code fence cap heapCap heapFence aligned below loHeap dstLow dstHigh atP atHeap run
#print axioms encode_header_prefix_writer_normal
end InitECandidate.Runtime
