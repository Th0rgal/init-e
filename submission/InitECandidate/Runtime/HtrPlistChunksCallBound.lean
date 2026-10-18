import InitECandidate.Runtime.HtrPlistChunksBound
import InitECandidate.Runtime.OriginalHtrPlistChunksCode
import InitECandidate.Runtime.PanFourWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original htr_plist_chunks calls add one entry tick to the full body bound.
Only the real input-size and heap-cap conditions are required for runtime. -/
theorem runBounded_htrPlistChunks_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer n limit out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word limit),.val (.word out)])
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPlistChunksCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_plist_chunks") arguments) (htrPlistChunksCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_plist_chunks") =
      some ([(ofString "roots",.one),(ofString "n",.one),(ofString "len",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_plist_chunks,.one) := by
    rw [code]
    exact originalRuntimeCode_htr_plist_chunks_lookup
  rw [pan_four_word_lookup state.code.lookup (ofString "htr_plist_chunks") (ofString "roots") (ofString "n")
    (ofString "len") (ofString "out") (sourceFunctionBody Guest.guestFn_htr_plist_chunks) pointer n limit out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrPlistChunks_body _ pointer n out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact heapLocal
  · exact small
  · exact heapBound
  · exact code
  · change htrPlistChunksCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrPlistChunks_call
end InitECandidate.Runtime
