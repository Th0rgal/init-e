import InitECandidate.Runtime.HeaderHashAfterHeaderBound
import InitECandidate.Runtime.EncodeHeaderWorkspaceGlobalClosure
import InitECandidate.Runtime.EncodeHeaderCallBound
import InitECandidate.Runtime.EncodeHeaderReturnedEnvelope
import InitECandidate.Runtime.HeapMarkDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def headerHashAfterMarkCost : Nat := encodeHeaderSourceCost+1+headerHashAfterHeaderCost
def headerHashSourceCost : Nat := 1+headerHashAfterMarkCost
/-- The real encode_header call supplies its actual returned encoded length and
retains the original Keccak workspace globals. -/
theorem header_hash_after_mark_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap length pointer pad output : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atH : s.locals.lookup (ofString "h")=some (.val (.word header)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (atState : s.globals.lookup (ofString "keccak_st")=some (.val (.word pointer)))
 (atPad : s.globals.lookup (ofString "keccak_pad")=some (.val (.word pad)))
 (atOut : s.locals.lookup (ofString "out")=some (.val (.word output)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0) (outputAligned : output.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : headerHashAfterMarkCost≤s.clock) :
 RunBounded s (headerHashAt 1) headerHashAfterMarkCost := by
 have stage : headerHashAt 1=.decCall (ofString "e") (.comb [.one,.one]) (ofString "encode_header")
  [.var .local (ofString "h")] (headerHashAt 2) := rfl
 rw [stage]
 have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) [.var .local (ofString "h")]=some [.val (.word header)] := by
  simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atH]
 apply RunBounded.decCall args budget
 intro body callee shape lookup
 have bounded:=encode_header_installed_body_bounded s header heap length DF body callee shape code fence cap heapFence
  atHeap heapCap aligned headerBelow atLength small lookup (by unfold headerHashAfterMarkCost at budget;omega)
 have same:=lookupCodeHOLFinite_installed_body s.code.lookup (ofString "encode_header") _ _ body _ shape _ callee
  (by rw [code];exact originalRuntimeCode_encodeHeader_lookup) lookup
 subst same
 rw [code] at lookup
 have bindings:=callee_eq originalRuntimeCode_encodeHeader_lookup lookup
 let entry:=callEntryStateHOLFinite s callee
 have atHeader : entry.locals.lookup (ofString "h")=some (.val (.word header)) := by
  simp [entry,callEntryStateHOLFinite,bindings,HolFiniteMapExact.lookup_update,FUPDATE]
 refine ⟨bounded,?_⟩
 intro value post returned remaining
 obtain ⟨start,encodedLength,rfl,_,encodedSmall⟩:=encode_header_returned_envelope entry post value header heap length DF
  code fence cap heapFence atHeader atHeap heapCap aligned headerBelow atLength returned
 have metadata:=evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_encode_header)
 rw [returned] at metadata
 have globalsKept (key : MlS) (member : key∈encodeHeaderWorkspaceGlobals) : post.globals.lookup key=s.globals.lookup key := by
  have kept:=evaluate_encode_header_workspace_global entry (sourceFunctionBody Guest.guestFn_encode_header) key member
   (by decide_cbv) code
  rw [returned] at kept
  exact kept
 apply header_hash_after_header_bounded
  (setVarHOLFinite (ofString "e") (.rStruct [.val (.word start),.val (.word encodedLength)]) {post with locals:=s.locals})
  pointer pad start encodedLength output (metadata.1.trans code)
 · change post.globals.lookup (ofString "keccak_st")=_
   rw [globalsKept _ (by simp [encodeHeaderWorkspaceGlobals])];exact atState
 · change post.globals.lookup (ofString "keccak_pad")=_
   rw [globalsKept _ (by simp [encodeHeaderWorkspaceGlobals])];exact atPad
 · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · simpa (config:={decide:=true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atOut
 · omega
 · exact outputAligned
 · exact remaining

/-- Complete actual original header_hash, with no encoded-length/callee-runtime
callback: the real encoder proves the length and the wide real Keccak is bounded. -/
theorem header_hash_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap length pointer pad output : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atH : s.locals.lookup (ofString "h")=some (.val (.word header)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (atState : s.globals.lookup (ofString "keccak_st")=some (.val (.word pointer)))
 (atPad : s.globals.lookup (ofString "keccak_pad")=some (.val (.word pad)))
 (atOut : s.locals.lookup (ofString "out")=some (.val (.word output)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0) (outputAligned : output.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : headerHashSourceCost≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_header_hash) headerHashSourceCost := by
 have stage : headerHashAt 0=.decCall (ofString "mark") .one (ofString "heap_mark") [] (headerHashAt 1) := rfl
 have reached:=evaluate_heapMark_declaration_reaches s (ofString "mark") heap (headerHashAt 1)
  code atHeap (by unfold headerHashSourceCost at budget;omega)
 rw [←stage] at reached
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (headerHashAt 0) headerHashSourceCost
 apply evaluate_reaches_terminal_bounded s _ _ _ 1 headerHashAfterMarkCost budget reached
 intro ready facts remaining
 obtain ⟨locals,memory,globals,installed,domain⟩:=facts
 apply header_hash_after_mark_bounded ready header heap length pointer pad output DF (installed.trans code)
 · rw [domain];exact fence
 · exact cap
 · exact heapFence
 · rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atH
 · rw [globals];exact atHeap
 · rw [globals];exact atState
 · rw [globals];exact atPad
 · rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atOut
 · exact heapCap
 · exact aligned
 · exact outputAligned
 · exact headerBelow
 · rw [memory];exact atLength
 · exact small
 · exact remaining
#print axioms header_hash_after_mark_bounded
#print axioms header_hash_body_bounded
end InitECandidate.Runtime
