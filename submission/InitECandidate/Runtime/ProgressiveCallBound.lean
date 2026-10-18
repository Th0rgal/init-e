import InitECandidate.Runtime.ProgressiveBodyBound
import InitECandidate.Runtime.OriginalProgressiveCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original progressive Merkle calls add one entry tick to the full body bound.
Only the real input-size and heap-cap conditions are required for runtime. -/
theorem runBounded_progressive_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer n out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word out)])
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : progressiveBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "merkleize_progressive") arguments) (progressiveBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "merkleize_progressive") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_merkleize_progressive,.one) := by
    rw [code]
    exact originalRuntimeCode_progressive_lookup
  rw [pan_three_word_lookup state.code.lookup (ofString "merkleize_progressive") (ofString "p") (ofString "n")
    (ofString "out") (sourceFunctionBody Guest.guestFn_merkleize_progressive) pointer n out
    (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  apply runBounded_progressive_body _ pointer n heap
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simp (config := {decide := true}) [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · exact small
  · exact heapLocal
  · exact heapBound
  · exact code
  · change progressiveBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_progressive_call
end InitECandidate.Runtime
