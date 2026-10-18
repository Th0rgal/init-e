import InitECandidate.Runtime.HtrPbytesBound
import InitECandidate.Runtime.OriginalHtrPbytesCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original htrPbytes Merkle calls add one entry tick to the full body bound.
Only the real input-size and heap-cap conditions are required for runtime. -/
theorem runBounded_htrPbytes_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPbytesBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_pbytes") arguments) (htrPbytesBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_pbytes") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_pbytes,.one) := by
    rw [code]
    exact originalRuntimeCode_htrPbytes_lookup
  rw [pan_three_word_lookup state.code.lookup (ofString "htr_pbytes") (ofString "p") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_pbytes) pointer n out
    (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrPbytes_body _ pointer n out heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact small
  · exact heapLocal
  · exact heapBound
  · exact code
  · change htrPbytesBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrPbytes_call
end InitECandidate.Runtime
