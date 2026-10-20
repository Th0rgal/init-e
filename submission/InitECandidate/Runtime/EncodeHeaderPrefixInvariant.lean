import InitECandidate.Runtime.EncodeHeaderPrefixWriter
import InitECandidate.Runtime.EncodeHeaderCursorIncrement
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
structure EncodeHeaderPrefixInvariant {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap lo watched length : BitVec 64) (DF : Nat) : Prop where
 code : s.code=originalRuntimeCode
 fence : Fence s.memaddrs DF
 atH : s.locals.lookup (ofString "h")=some (.val (.word header))
 atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap))
 atLength : s.memory watched=.word length
 cursor : ∃dst : BitVec 64,s.locals.lookup (ofString "p")=some (.val (.word dst)) ∧lo.toNat≤dst.toNat ∧dst.toNat≤DF+8

/-- The real normal writer call followed by its real p increment retains the
header-length word and every fact needed at the next original writer. -/
theorem encode_header_prefix_writer_advance {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (writer : EncodeHeaderPrefixWriter) (input : ExpHOL 64)
 (header heap lo watched length : BitVec 64) (DF : Nat)
 (valid : EncodeHeaderPrefixInvariant s header heap lo watched length DF)
 (cap : DF≤2^62) (heapCap : heap.toNat≤33806089496) (heapFence : 33806089496≤DF)
 (aligned : lo.toNat%8=0) (below : watched.toNat<lo.toNat) (loHeap : lo.toNat≤heap.toNat)
 (run : evaluateHOLFiniteState s (encodeHeaderPrefixWriterCall writer input)=(none,post)) :
 ∃dst written : BitVec 64,
 evaluateHOLFiniteState post (.assign .local (ofString "p")
  (.op .add [.var .local (ofString "p"),.var .local (ofString "w")]))=
  (none,setVarHOLFinite (ofString "p") (.val (.word (dst+written))) post) ∧
 EncodeHeaderPrefixInvariant (setVarHOLFinite (ofString "p") (.val (.word (dst+written))) post)
  header heap lo watched length DF := by
 obtain ⟨dst,atP,low,high⟩:=valid.cursor
 obtain ⟨written,fits,locals,memory,globals⟩:=encode_header_prefix_writer_normal s post writer input dst heap lo watched DF
  valid.code valid.fence cap heapCap heapFence aligned below loHeap low high atP valid.atHeap run
 have nextP : post.locals.lookup (ofString "p")=some (.val (.word dst)) := by
  rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atP
 have nextW : post.locals.lookup (ofString "w")=some (.val (.word written)) := by
  rw [locals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
 have increment:=encode_header_cursor_increment post dst written DF cap nextP nextW fits
 have metadata:=evaluateHOLFiniteState_metadata s (encodeHeaderPrefixWriterCall writer input)
 rw [run] at metadata
 refine ⟨dst,written,increment.1,?_,?_,?_,?_,?_,?_⟩
 · exact metadata.1.trans valid.code
 · change Fence post.memaddrs DF;rw [metadata.2.1];exact valid.fence
 · change (post.locals.update (ofString "p",.val (.word (dst+written)))).lookup (ofString "h")=_
   rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using valid.atH
 · change post.globals.lookup (ofString "heap_ptr")=_;rw [globals];exact valid.atHeap
 · change post.memory watched=_;rw [memory];exact valid.atLength
 · refine ⟨dst+written,?_,?_,?_⟩
   · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
   · rw [increment.2];omega
   · rw [increment.2];exact fits
#print axioms encode_header_prefix_writer_advance
end InitECandidate.Runtime
