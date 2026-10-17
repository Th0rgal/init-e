import InitECandidate.Runtime.HashTableSetLookupFailureTerminalSupportedNoTimeout
import InitECandidate.Runtime.HashTableSetLookupLinkedSupported
import InitECandidate.Runtime.HashTableReady
import InitECandidate.Runtime.DeclarationResultUnique
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.set_unsafe_growth_supported_dichotomy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 9 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496)
    (notSafe : ¬ AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (loadFactor : capacity.toNat < (count.toNat + 1) * 2) :
    (∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer post ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 9 ∧ post.clock ≤ state.clock) ∨
    ((evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ none ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ some .timeOut ∧
    (∀ output : ValueHOL 64, (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ some (.returned output)) ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).1 ≠ some .continue ∧
    state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock + 2 * capacity.toNat + 9 ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_set)).2.clock ≤ state.clock) := by
  obtain ⟨found,ready,_,decl,failed⟩ := invariant.live.arrays.set_lookup_failure_terminal_supported_no_timeout state keyLength table pointer keys stride capacity used values order orderPos count key value bits supported
    tableLocal keyLocal valueLocal keyAligned keyWords keyBytes budget heap pointerBound notSafe loadFactor
  obtain ⟨existing,other,_,_,otherDecl,present⟩ := invariant.live.arrays.set_lookup_supported_linked_entries state keyLength table keys stride capacity used values order orderPos count key value bits supported
    tableLocal keyLocal valueLocal keyAligned keyWords keyBytes (by omega) invariant.live.entries invariant.valuesWord invariant.reverse invariant.linked
  have equal := declaration_word_result_unique state ready other (ofString "i") (ofString "htab_find_slot")
    [.var .local (ofString "t"),.var .local (ofString "key")] found existing decl otherDecl
  by_cases missing : found = capacity
  · exact Or.inr (failed missing)
  · have different : existing ≠ capacity := by rw [← equal]; exact missing
    obtain ⟨post,run,arrays,entries,valuesWord,reverse,linked,cost,remaining,globals,code,domain,endian⟩ := present different
    have ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer post :=
      ⟨⟨arrays,entries,invariant.live.frontier.after_globals state post orderPos capacity pointer globals⟩,valuesWord,reverse,linked,invariant.ordering⟩
    exact Or.inl ⟨post,run,ready,globals,code,domain,endian,by omega,remaining⟩

#print axioms HashTableReady.set_unsafe_growth_supported_dichotomy
end InitECandidate.Runtime
