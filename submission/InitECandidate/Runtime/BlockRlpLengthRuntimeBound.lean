import InitECandidate.Runtime.BlockRlpLengthLoopsBound
import InitECandidate.Runtime.EncodeHeaderCallBound
import InitECandidate.Runtime.HeapMarkDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
import InitECandidate.Runtime.VmFn_heap_release
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def blockRlpLengthAfterHeaderCost := 1+blockRlpLengthLoopSuffixCost
def blockRlpLengthAfterMarkCost := encodeHeaderSourceCost+1+blockRlpLengthAfterHeaderCost
def blockRlpLengthSourceCost := 1+blockRlpLengthAfterMarkCost

theorem block_rlp_length_after_header_bounded :
 ProgBounded (blockRlpLengthLoopAt 2) blockRlpLengthAfterHeaderCost := by
 have stage : blockRlpLengthLoopAt 2=.seq
  (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (blockRlpLengthLoopAt 3) := rfl
 rw [stage]
 intro F state code budget
 exact ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) block_rlp_length_loop_suffix_bounded state code budget

theorem block_rlp_length_after_mark_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap length : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeader : s.locals.lookup (ofString "hdr")=some (.val (.word header)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : blockRlpLengthAfterMarkCost≤s.clock) :
 RunBounded s (blockRlpLengthLoopAt 1) blockRlpLengthAfterMarkCost := by
 have stage : blockRlpLengthLoopAt 1=.decCall (ofString "he") (.comb [.one,.one]) (ofString "encode_header")
  [.var .local (ofString "hdr")] (blockRlpLengthLoopAt 2) := rfl
 rw [stage]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "hdr")]=some [.val (.word header)] := by
  simp [evalListHOLFinite_eq_toExact,evalListHOLExact,evalHOLExact,atHeader]
 apply RunBounded.decCall args budget
 intro body callee shape lookup
 have bound:=encode_header_installed_body_bounded s header heap length DF body callee shape code fence cap heapFence
  atHeap heapCap aligned headerBelow atLength small lookup (by unfold blockRlpLengthAfterMarkCost at budget;omega)
 refine ⟨bound,?_⟩
 intro value post returned remaining
 have metadata:=evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) body
 rw [returned] at metadata
 exact block_rlp_length_after_header_bounded _ (metadata.1.trans code) remaining

/-- Complete actual block RLP length function. The original header's extra-data
 length is the only variable byte-writer bound; transaction/withdrawal length
 loops use their actual finite counter ranks, and allocation rejection is included. -/
theorem block_rlp_length_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap length : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF) (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atHeader : s.locals.lookup (ofString "hdr")=some (.val (.word header)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : blockRlpLengthSourceCost≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_block_rlp_length) blockRlpLengthSourceCost := by
 have stage : blockRlpLengthLoopAt 0=.decCall (ofString "mark") .one (ofString "heap_mark") [] (blockRlpLengthLoopAt 1) := rfl
 have reached:=evaluate_heapMark_declaration_reaches s (ofString "mark") heap (blockRlpLengthLoopAt 1)
  code atHeap (by unfold blockRlpLengthSourceCost at budget;omega)
 rw [←stage] at reached
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (blockRlpLengthLoopAt 0) blockRlpLengthSourceCost
 apply evaluate_reaches_terminal_bounded s _ _ _ 1 blockRlpLengthAfterMarkCost budget reached
 intro ready facts remaining
 obtain ⟨locals,memory,globals,installed,domain⟩:=facts
 apply block_rlp_length_after_mark_bounded ready header heap length DF (installed.trans code)
 · rw [domain];exact fence
 · exact cap
 · exact heapFence
 · rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atHeader
 · rw [globals];exact atHeap
 · exact heapCap
 · exact aligned
 · exact headerBelow
 · rw [memory];exact atLength
 · exact small
 · exact remaining
#print axioms block_rlp_length_after_header_bounded
#print axioms block_rlp_length_body_bounded
end InitECandidate.Runtime
