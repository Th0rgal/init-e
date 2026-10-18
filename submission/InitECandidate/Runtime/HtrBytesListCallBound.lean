import InitECandidate.Runtime.HtrBytesListBound
import InitECandidate.Runtime.OriginalHtrBytesListCode
import InitECandidate.Runtime.PanFourWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original htr_bytes_list calls add one entry tick to the full body bound.
Only the real input-size and heap-cap conditions are required for runtime. -/
theorem runBounded_htrBytesList_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer n limit out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word limit),.val (.word out)])
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrBytesListBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_bytes_list") arguments) (htrBytesListBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_bytes_list") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "limit_chunks",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bytes_list,.one) := by
    rw [code]
    exact originalRuntimeCode_htr_bytes_list_lookup
  rw [pan_four_word_lookup state.code.lookup (ofString "htr_bytes_list") (ofString "p") (ofString "n")
    (ofString "limit_chunks") (ofString "out") (sourceFunctionBody Guest.guestFn_htr_bytes_list) pointer n limit out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrBytesList_body _ pointer n limit out heap
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "p" by decide,show ofString "limit_chunks" ≠ ofString "p" by decide,
      show ofString "n" ≠ ofString "p" by decide]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "n" by decide,show ofString "limit_chunks" ≠ ofString "n" by decide]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "limit_chunks" by decide]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact small
  · exact heapLocal
  · exact heapBound
  · exact code
  · change htrBytesListBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrBytesList_call
end InitECandidate.Runtime
