import InitECandidate.Runtime.MerkleizeBodyBound
import InitECandidate.Runtime.OriginalMerkleizeCode
import InitECandidate.Runtime.PanFourWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual original merkleize calls add one entry tick to the full body bound.
Only the real input-size and heap-cap conditions are required for runtime. -/
theorem runBounded_merkleize_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer n limit out heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word n),.val (.word limit),.val (.word out)])
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merkleBodyCost + 1 ≤ state.clock) :
    RunBounded state (.call (some (destination,none)) (ofString "merkleize") arguments) (merkleBodyCost + 1) := by
  refine RunBounded.call args budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "merkleize") =
      some ([(ofString "p",.one),(ofString "n",.one),(ofString "limit",.one),(ofString "out",.one)],
        sourceFunctionBody Guest.guestFn_merkleize,.one) := by
    rw [code]
    exact originalRuntimeCode_merkleize_lookup
  rw [pan_four_word_lookup state.code.lookup (ofString "merkleize") (ofString "p") (ofString "n")
    (ofString "limit") (ofString "out") (sourceFunctionBody Guest.guestFn_merkleize) pointer n limit out
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed] at lookup
  cases lookup
  apply runBounded_merkleize_body _ pointer n limit heap
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "p" by decide,show ofString "limit" ≠ ofString "p" by decide,
      show ofString "n" ≠ ofString "p" by decide]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "n" by decide,show ofString "limit" ≠ ofString "n" by decide]
  · simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "limit" by decide]
  · exact small
  · exact heapLocal
  · exact heapBound
  · exact code
  · change merkleBodyCost ≤ state.clock - 1
    omega

#print axioms runBounded_merkleize_call
end InitECandidate.Runtime
