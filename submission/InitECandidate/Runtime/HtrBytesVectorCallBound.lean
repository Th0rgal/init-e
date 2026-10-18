import InitECandidate.Runtime.HtrBytesVectorBodyBound
import InitECandidate.Runtime.OriginalHtrBytesVectorCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original htrBytesVector Merkle calls add one entry tick to the full body bound.
Only the real input-size and heap-cap conditions are required for runtime. -/
theorem runBounded_htrBytesVector_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrBytesVectorBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_bytes_vector") arguments) (htrBytesVectorBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_bytes_vector") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_bytes_vector,.one) := by
    rw [code]
    exact originalRuntimeCode_htrBytesVector_lookup
  rw [pan_three_word_lookup state.code.lookup (ofString "htr_bytes_vector") (ofString "p") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_bytes_vector) pointer n out
    (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrBytesVector_body _ pointer n out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact heapLocal
  · exact small
  · exact heapBound
  · exact code
  · change htrBytesVectorBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrBytesVector_call
end InitECandidate.Runtime
