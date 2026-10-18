import InitECandidate.Runtime.HtrWithdrawalAllocationBound
import InitECandidate.Runtime.MerklePositiveBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrWithdrawalBodyCost : Nat := 1 + htrWithdrawalAllocationCost

theorem runBounded_htrWithdrawal_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (w out heap : BitVec 64)
    (input : state.locals.lookup (ofString "w") = some (.val (.word w)))
    (count : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (heapLocal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : htrWithdrawalBodyCost ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_htr_withdrawal) htrWithdrawalBodyCost := by
  rw [sourceFunctionBody_eq_structural]
  change RunBounded state (htrWithdrawalAt 0) htrWithdrawalBodyCost
  rw [source_htrWithdrawal_mark]
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
    exact runBounded_htrWithdrawal_allocation next w out heap
      ((keep _ (by decide)).trans input) ((keep _ (by decide)).trans count)
      (by change post.globals.lookup _ = _; rw [globals]; exact heapLocal)
      heapBound (meta'.1.trans code) remaining

#print axioms runBounded_htrWithdrawal_body
end InitECandidate.Runtime
