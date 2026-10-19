import InitECandidate.Runtime.NodedbBodyBound
import InitECandidate.Runtime.OriginalNodedbBuildCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual installed node-database builder call is bounded in every outcome
from the decoded input geometry, for any destination without an error handler. -/
theorem runBounded_nodedb_call {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer total array statePad pad output : BitVec 64)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some [.val (.word array),.val (.word total)])
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (small : total.toNat ≤ 134217712)
    (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ pointer.toNat)
    (stateEnd : statePad.toNat + 200 ≤ array.toNat) (padEnd : pad.toNat + 136 ≤ array.toNat)
    (outputEnd : output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (slices : ∀ j : BitVec 64, j.toNat < total.toNat → ∃ source size : BitVec 64,
      s.memaddrs (array + j * (16#64)) ∧ s.memaddrs (array + j * (16#64) + (8#64)) ∧
      s.memory (array + j * (16#64)) = .word source ∧ s.memory (array + j * (16#64) + (8#64)) = .word size ∧
      size.toNat ≤ 134217712)
    (budget : nodedbBodyCost total + 1 ≤ s.clock) :
    RunBounded s (.call (some (destination,none)) (ofString "nodedb_build") arguments) (nodedbBodyCost total + 1) := by
  refine RunBounded.call args budget ?_
  intro body callee returnShape lookup
  have installed : s.code.lookup (ofString "nodedb_build") =
      some ([(ofString "slice_arr",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_nodedb_build,.one) := by
    rw [code]; exact originalRuntimeCode_nodedbBuild_lookup
  rw [pan_two_word_lookup s.code.lookup (ofString "nodedb_build") (ofString "slice_arr") (ofString "n")
    (sourceFunctionBody Guest.guestFn_nodedb_build) array total (by decide) installed] at lookup
  cases lookup
  let entry := callEntryStateHOLFinite s
    ((HolFiniteMapExact.empty.update (ofString "slice_arr",.val (.word array))).update (ofString "n",.val (.word total)))
  exact runBounded_nodedb_body entry pointer total array statePad pad output code atHeap aligned capped
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    atState atPad atOutput small outputAligned arrayEnd stateEnd padEnd outputEnd arena slices
    (by change nodedbBodyCost total ≤ s.clock - 1; omega)

#print axioms runBounded_nodedb_call
end InitECandidate.Runtime
