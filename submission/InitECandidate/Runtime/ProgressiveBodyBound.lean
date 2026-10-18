import InitECandidate.Runtime.ProgressiveAllocationBound
import InitECandidate.Runtime.MerklePositiveBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def progressiveBodyCost : Nat := 1 + (2 + (2 + progressiveLoopsCost))

theorem source_progressive_mark : progressiveAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (progressiveAt 1) := by rfl

theorem runBounded_progressive_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer n heap : BitVec 64)
    (input : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (count : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (small : n.toNat ≤ 134217712)
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : progressiveBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_merkleize_progressive) progressiveBodyCost := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (progressiveAt 0) progressiveBodyCost
  rw [source_progressive_mark]
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
    exact runBounded_progressive_roots next pointer n heap
      ((keep _ (by decide)).trans input) ((keep _ (by decide)).trans count)
      (by change post.globals.lookup _ = _; rw [globals]; exact heapLocal)
      small heapBound (meta'.1.trans code) remaining

#print axioms source_progressive_mark
#print axioms runBounded_progressive_body
end InitECandidate.Runtime
