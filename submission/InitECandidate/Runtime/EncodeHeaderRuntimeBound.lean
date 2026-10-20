import InitECandidate.Runtime.EncodeHeaderFirstWriterBound
import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.ReachesTerminalBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
def encodeHeaderSourceCost : Nat := 2+encodeHeaderFirstWriterCost
/-- Complete original encode_header, including inaccessible memory and failed
allocations. Its sole variable byte count is the original h136 word. -/
theorem encode_header_body_bounded {F : Type} (s : PanSemStateFiniteExact 64 F)
 (header heap length : BitVec 64) (DF : Nat)
 (code : s.code=originalRuntimeCode) (fence : Fence s.memaddrs DF)
 (cap : DF≤2^62) (heapFence : 33806089496≤DF)
 (atH : s.locals.lookup (ofString "h")=some (.val (.word header)))
 (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
 (heapCap : heap.toNat≤33806089496) (aligned : heap.toNat%8=0)
 (headerBelow : header.toNat+144≤heap.toNat)
 (atLength : s.memory (header+136)=.word length) (small : length.toNat≤2^62)
 (budget : encodeHeaderSourceCost≤s.clock) :
 RunBounded s (sourceFunctionBody Guest.guestFn_encode_header) encodeHeaderSourceCost := by
 have stage0 : encodeHeaderAt 0=.decCall (ofString "buf") .one (ofString "alloc") [.const 1024] (encodeHeaderAt 1) := rfl
 have reached:=evaluate_allocation_declaration_reaches s (.const 1024) (ofString "buf") heap 1024 (encodeHeaderAt 1)
  (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact]) code atHeap heapCap (by unfold encodeHeaderSourceCost at budget;omega)
 rw [←stage0] at reached
 rw [sourceFunctionBody_eq_structural]
 change RunBounded s (encodeHeaderAt 0) encodeHeaderSourceCost
 apply evaluate_reaches_terminal_bounded s _ _ _ 2 encodeHeaderFirstWriterCost budget reached
 intro ready allocation remaining
 obtain ⟨locals,memory,installed,domain,globals,nextCap,covers,nextAligned⟩:=allocation
 let nextHeap:=allocationEnd heap (1024#64)
 have nextCapBound : nextHeap.toNat≤33806089496 := nextCap
 have heapLow : heap.toNat≤nextHeap.toNat := by change heap.toNat+1024≤nextHeap.toNat at covers;omega
 have watchedNat : (header+136).toNat=header.toNat+136 := by
  rw [BitVec.toNat_add]
  apply Nat.mod_eq_of_lt
  change header.toNat+136<2^64
  omega
 have cursorNat : (heap+9).toNat=heap.toNat+9 := by
  rw [BitVec.toNat_add]
  apply Nat.mod_eq_of_lt
  change heap.toNat+9<2^64
  omega
 have stage1 : encodeHeaderAt 1=.dec (ofString "p") .one
  (.op .add [.var .local (ofString "buf"),.const 9]) (encodeHeaderAt 2) := rfl
 rw [stage1]
 have buffer : ready.locals.lookup (ofString "buf")=some (.val (.word heap)) := by
  rw [locals];simp [HolFiniteMapExact.lookup_update,FUPDATE]
 apply RunBounded.decWord ready (ofString "p") _ (heap+9)
 · simp [evalHOLExact,evalListHOLExact,buffer,wordOpHOL,wordOp,valueIsWord,valueWord]
 · apply encode_header_first_writer_bounded _ header nextHeap heap length DF
   · constructor
     · exact installed.trans code
     · change Fence ready.memaddrs DF;rw [domain];exact fence
     · change (ready.locals.update (ofString "p",.val (.word (heap+9)))).lookup (ofString "h")=_
       rw [locals];simpa (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE] using atH
     · change ready.globals.lookup (ofString "heap_ptr")=_
       rw [globals];simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nextHeap]
     · change ready.memory (header+136)=_;rw [memory];exact atLength
     · refine ⟨heap+9,?_,?_,?_⟩
       · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
       · rw [cursorNat];omega
       · rw [cursorNat];change heap.toNat+1024≤nextHeap.toNat at covers;omega
   · exact cap
   · exact nextCap
   · exact heapFence
   · exact aligned
   · rw [watchedNat];omega
   · exact heapLow
   · exact small
   · exact remaining
#print axioms encode_header_body_bounded
end InitECandidate.Runtime
