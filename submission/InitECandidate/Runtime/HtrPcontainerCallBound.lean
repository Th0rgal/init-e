import InitECandidate.Runtime.HtrPcontainerBodyBound
import InitECandidate.Runtime.OriginalHtrPcontainerCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original htrPcontainer Merkle calls add one entry tick to the full body bound.
Only the real input-size and heap-cap conditions are required for runtime. -/
theorem runBounded_htrPcontainer_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrPcontainerBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "htr_pcontainer") arguments) (htrPcontainerBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "htr_pcontainer") =
      some ([(ofString "ch",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_htr_pcontainer,.one) := by
    rw [code]
    exact originalRuntimeCode_htrPcontainer_lookup
  rw [pan_three_word_lookup state.code.lookup (ofString "htr_pcontainer") (ofString "ch") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_htr_pcontainer) pointer n out
    (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  apply runBounded_htrPcontainer_body _ pointer n heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact small
  · exact heapLocal
  · exact heapBound
  · exact code
  · change htrPcontainerBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_htrPcontainer_call
end InitECandidate.Runtime
