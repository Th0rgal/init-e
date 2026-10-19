import InitECandidate.Runtime.NodedbEmptyBound
import InitECandidate.Runtime.OriginalNodedbBuildCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Empty input arrays, including pointer zero, need no array or hash-buffer
geometry to bound the actual installed builder call. -/
theorem runBounded_nodedb_empty_call {F : Type} (s : PanSemStateFiniteExact 64 F) (array pointer : BitVec 64)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments =
      some [.val (.word array),.val (.word (0#64))])
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (budget : 46 ≤ s.clock) :
    RunBounded s (.call (some (destination,none)) (ofString "nodedb_build") arguments) 46 := by
  refine RunBounded.call (bodyCost := 45) args budget ?_
  intro body callee returnShape lookup
  have installed : s.code.lookup (ofString "nodedb_build") =
      some ([(ofString "slice_arr",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_nodedb_build,.one) := by
    rw [code]; exact originalRuntimeCode_nodedbBuild_lookup
  rw [pan_two_word_lookup s.code.lookup (ofString "nodedb_build") (ofString "slice_arr") (ofString "n")
    (sourceFunctionBody Guest.guestFn_nodedb_build) array (0#64) (by decide) installed] at lookup
  cases lookup
  exact runBounded_nodedb_empty_body _ pointer code
    (by simp [callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) atHeap aligned capped arena
    (by change 45 ≤ s.clock - 1; omega)

#print axioms runBounded_nodedb_empty_call
end InitECandidate.Runtime
