import InitECandidate.Runtime.HashTableSetLookupFailure32
import InitECandidate.Runtime.DeclarationResultUnique
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.set_unsafe_growth_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
    state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock + 2 * capacity.toNat + 9 ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock := by
  obtain ⟨found,ready,_,decl,failed⟩ := invariant.set_lookup_failure state table pointer keys stride capacity used values order orderPos count key value bits
    tableLocal keyLocal valueLocal keyAligned keyDomain budget heap pointerBound notSafe loadFactor
  obtain ⟨existing,other,_,_,otherDecl,present⟩ := invariant.set_lookup state table keys stride capacity used values order orderPos count key value bits
    tableLocal keyLocal valueLocal keyAligned keyDomain (by omega)
  have equal := declaration_word_result_unique state ready other (ofString "i") (ofString "htab_find_slot")
    [.var .local (ofString "t"),.var .local (ofString "key")] found existing decl otherDecl
  by_cases missing : found = capacity
  · exact failed missing
  · have different : existing ≠ capacity := by rw [← equal]; exact missing
    obtain ⟨post,run,_,cost,remaining,_⟩ := present different
    rw [run]
    dsimp only
    exact ⟨by simp,by omega,remaining⟩

#print axioms HashTableArraysInvariant32.set_unsafe_growth_bounded
end InitECandidate.Runtime
