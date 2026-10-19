import InitECandidate.Runtime.NodedbCallBound
import InitECandidate.Runtime.NodedbEmptyCallBound
import InitECandidate.Runtime.DecodeBytesListInputContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The caller may use its actual decoded-list contract directly. The zero
array pointer used for empty lists needs no hash-workspace geometry. -/
theorem runBounded_nodedb_decoded_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (heap total array input inputLength statePad pad output : BitVec 64)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some [.val (.word array),.val (.word total)])
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (aligned : heap.toNat % 8 = 0) (capped : heap.toNat ≤ 33806089496)
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (decoded : RlpSliceInputPrefix s array input inputLength total.toNat)
    (countBound : total.toNat ≤ inputLength.toNat / 4) (inputSmall : inputLength.toNat ≤ 134217712)
    (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ heap.toNat)
    (windows : total ≠ 0 → statePad.toNat + 200 ≤ array.toNat ∧ pad.toNat + 136 ≤ array.toNat ∧
      output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → heap.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (budget : nodedbBodyCost total + 1 ≤ s.clock) :
    RunBounded s (.call (some (destination,none)) (ofString "nodedb_build") arguments) (nodedbBodyCost total + 1) := by
  by_cases empty : total = 0
  · subst total
    have large : 46 ≤ nodedbBodyCost (0#64) + 1 := by unfold nodedbBodyCost nodedbTailCost; omega
    exact (runBounded_nodedb_empty_call s array heap destination arguments (by simpa using args) code atHeap
      aligned capped arena (large.trans budget)).weaken large
  · obtain ⟨stateEnd,padEnd,outputEnd⟩ := windows empty
    apply runBounded_nodedb_call s heap total array statePad pad output destination arguments args code atHeap aligned capped
      atState atPad atOutput (by omega) outputAligned arrayEnd stateEnd padEnd outputEnd arena ?_ budget
    intro j inside
    obtain ⟨src,len,valid⟩ := decoded j inside
    exact ⟨src,len,valid.readable.pointerDomain,valid.readable.lengthDomain,valid.readable.pointerCell,
      valid.readable.lengthCell,(valid.length_bound s array j src len input inputLength).trans inputSmall⟩

#print axioms runBounded_nodedb_decoded_call
end InitECandidate.Runtime
