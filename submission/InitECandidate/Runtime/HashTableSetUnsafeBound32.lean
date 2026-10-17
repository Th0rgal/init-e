import InitECandidate.Runtime.HashTableReady32
import InitECandidate.Runtime.HashTableSetLookupFailure32
import InitECandidate.Runtime.HashTableSetAboveThresholdLinkedEntries32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An unsafe growth plan still gives a finite set bound: an existing key is
updated, while a missing key terminates at the original failing allocation. -/
theorem HashTableReady32.set_unsafe_above {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 9 ≤ state.clock)
    (notSafe : ¬AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (above : capacity.toNat < (items.toNat + 1) * 2) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock + 2 * capacity.toNat + 9 ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock := by
  obtain ⟨found,lookupState,_,decl,failure⟩ := ready.live.arrays.set_lookup_failure state table pointer keys stride capacity used values order orderPos items key value bits
    t k v keyAligned keyDomain budget ready.live.frontier.heap ready.live.frontier.bounded notSafe above
  obtain ⟨existing,other,_,_,otherDecl,present⟩ := ready.live.arrays.set_lookup_linked_entries state table keys stride capacity used values order orderPos items key value bits
    t k v keyAligned keyDomain (by omega) ready.live.entries ready.valuesWord ready.reverse ready.linked
  have equal := declaration_word_result_unique state lookupState other (ofString "i") (ofString "htab_find_slot")
    [.var .local (ofString "t"),.var .local (ofString "key")] found existing decl otherDecl
  by_cases missing : found = capacity
  · exact failure missing
  · have different : existing ≠ capacity := by rw [← equal]; exact missing
    obtain ⟨post,run,_,_,_,_,_,cost,remaining,_⟩ := present different
    rw [run]
    dsimp only
    exact ⟨by simp,by omega,remaining⟩

#print axioms HashTableReady32.set_unsafe_above
end InitECandidate.Runtime
