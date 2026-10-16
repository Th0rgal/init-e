import InitECandidate.Runtime.HashTableSetMissingFailure32
import InitECandidate.Runtime.HashTableSetLookupExistingOrder32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_lookup_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 9 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (notSafe : ¬ AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      (∀ continuation, evaluateHOLFiniteState state
        (.decCall (ofString "i") .one (ofString "htab_find_slot")
          [.var .local (ofString "t"),.var .local (ofString "key")] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "i") (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "i",state.locals.lookup (ofString "i")))}))) ∧
      (found = capacity →
        (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
        state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock + 2 * capacity.toNat + 9 ∧
        (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal]
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,valid,decl⟩ :=
    invariant.find state table keys stride capacity used values order orderPos count key bits _ _ arguments keyAligned keyDomain (by omega)
  refine ⟨found,ready,inside,decl (ofString "i"),?_⟩
  intro same
  let entered := setVarHOLFinite (ofString "i") (.val (.word found)) ready
  have validEntry := valid.after_read ready entered table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have different : ofString "i" ≠ ofString "t" := by decide
  have t : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals,tableLocal]
  have sentinel : entered.locals.lookup (ofString "i") = some (.val (.word capacity)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same]
  have selected := evaluate_hashSet_missing_tail entered table capacity hashSetMissing t sentinel
    (validEntry.header_domain entered table keys stride capacity used values order orderPos count bits 16 (by decide)) validEntry.cell16
  have heapEntry : entered.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)) := by
    change ready.globals.lookup _ = _
    rw [globals]; exact heap
  obtain ⟨_,terminal,tailCost,tailRemaining⟩ := validEntry.set_missing_failure entered table pointer keys stride capacity used values order orderPos count bits
    heapEntry pointerBound (by change 5 ≤ ready.clock; omega) notSafe t loadFactor
  rw [source_hashSet_existing,decl,selected]
  dsimp only
  refine ⟨terminal,?_,?_⟩
  · change state.clock ≤ (evaluateHOLFiniteState entered hashSetMissing).2.clock + 2 * capacity.toNat + 9
    change ready.clock ≤ (evaluateHOLFiniteState entered hashSetMissing).2.clock + 7 at tailCost
    omega
  · change (evaluateHOLFiniteState entered hashSetMissing).2.clock ≤ state.clock
    change (evaluateHOLFiniteState entered hashSetMissing).2.clock ≤ ready.clock at tailRemaining
    omega

#print axioms HashTableArraysInvariant32.set_lookup_failure
end InitECandidate.Runtime
