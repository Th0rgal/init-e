import InitECandidate.Runtime.MerkleAllocationBound
import InitECandidate.Runtime.VmFn_heap_mark
import InitECandidate.Runtime.PanDecCallReadFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merklePositiveCost : Nat := 1 + merkleAllocationCost

theorem source_merkleMark : merkleizeAt 4 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (merkleizeAt 5) := by rfl

theorem heapMark_readOnly : readOnlyMemory (sourceFunctionBody Guest.guestFn_heap_mark) = true := by
  rw [sourceFunctionBody_eq_structural]
  rfl

/-- The complete original positive-count branch: mark, size computation,
allocation (including failure), copy, zero-fill, levels, padding and return. -/
theorem runBounded_merklePositive {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n dn target heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (depth : state.locals.lookup (ofString "dn") = some (.val (.word dn)))
    (limit : state.locals.lookup (ofString "target") = some (.val (.word target)))
    (lengths : MerkleChunkLengths n ((1#64) <<< dn.toNat))
    (depthBound : dn.toNat ≤ 27) (targetBound : target.toNat ≤ 63)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : merklePositiveCost ≤ state.clock) :
    RunBounded state (merkleizeAt 4) merklePositiveCost := by
  rw [source_merkleMark]
  refine RunBounded.decCall (by rfl) budget ?_
  intro body locals returnShape lookup
  have installed : state.code.lookup (ofString "heap_mark") =
      some ([],sourceFunctionBody Guest.guestFn_heap_mark,.one) := by
    rw [code]
    exact vmLookup_heap_mark
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "heap_mark") []
    (sourceFunctionBody Guest.guestFn_heap_mark) body .one returnShape [] locals installed lookup
  subst same
  constructor
  · exact RunBounded.ofProg
      (ProgBounded.straight _ (by rw [sourceFunctionBody_eq_structural]; rfl)) code (Nat.zero_le _)
  · intro value post run remaining
    have meta' := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals)
      (sourceFunctionBody Guest.guestFn_heap_mark)
    have globals := evaluate_readOnly_globals _ heapMark_readOnly (callEntryStateHOLFinite state locals)
    rw [run] at meta' globals
    change post.globals = state.globals at globals
    let next := setVarHOLFinite (ofString "mark") value {post with locals := state.locals}
    have keep (key : MlS) (different : key ≠ ofString "mark") :
        next.locals.lookup key = state.locals.lookup key := by
      simp [next,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
    exact runBounded_merkleSizeAllocation next pointer n dn target heap
      ((keep _ (by decide)).trans input) ((keep _ (by decide)).trans count)
      ((keep _ (by decide)).trans depth) ((keep _ (by decide)).trans limit)
      lengths depthBound targetBound
      (by change post.globals.lookup _ = _; rw [globals]; exact heapLocal)
      heapBound (meta'.1.trans code) remaining

#print axioms source_merkleMark
#print axioms heapMark_readOnly
#print axioms runBounded_merklePositive
end InitECandidate.Runtime
