import InitECandidate.Runtime.HashTableArraysLinkedInsert32
import InitECandidate.Runtime.HashTableArraysFind32
import InitECandidate.Runtime.HashSetGrowthGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original missing-key suffix below the growth threshold executes its
actual insertion call and preserves the table invariant with successor count. -/
theorem HashTableArraysInvariant32.set_missing_no_growth_linked_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (count.toNat + 1) * 2 ≤ capacity.toNat)
    (budget : capacity.toNat + 35 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (linked : HashOrderLinked used order orderPos capacity count state)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state hashSetMissing = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity (count + 1) post ∧
      HashOrderLinked used order orderPos capacity (count + 1) post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have condition := eval_hashSet_growth_false state table capacity count tableLocal
    (invariant.header_domain state table keys stride capacity used values order orderPos count bits 16 (by decide)) invariant.cell16
    (invariant.header_domain state table keys stride capacity used values order orderPos count bits 24 (by decide)) invariant.cell24 loadFactor
  have selected : evaluateHOLFiniteState state
      (.ite hashSetGrowthCondition (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip) =
      (none,state) := by
    rw [evaluateHOLFiniteState_ite,condition]
    simp [evaluateHOLFiniteState_skip]
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,tableLocal,keyLocal,valueLocal]
  obtain ⟨post,insert,valid,ordered,words,reverse,linkedAfter,cost,remaining,_,globals,addresses,endian⟩ :=
    invariant.insert_all_entries_linked state table keys stride capacity used values order orderPos count key value bits _ _ _ arguments keyAligned sourceWordDomain sourceByteDomain (by omega) budget entries valueEntries reverseEntries linked keysBeforeValues
  have returned : evaluateHOLFiniteState post (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite post,?_,valid.after_read post _ table keys stride capacity used values order orderPos (count + 1) bits rfl rfl rfl rfl,
    ordered.after_memory post _ order capacity (count + 1) rfl,
    words.after_read post _ used values capacity rfl rfl rfl,
    reverse.after_read post _ used orderPos capacity (count + 1) rfl rfl rfl,
    linkedAfter.after_read post _ used order orderPos capacity (count + 1) rfl rfl rfl,
    cost,remaining,globals,?_,addresses,endian⟩
  · rw [source_hashSet_missing]
    exact evaluate_seq_none selected (evaluate_seq_none insert returned)
  · exact valid.code.trans invariant.code.symm

#print axioms HashTableArraysInvariant32.set_missing_no_growth_linked_entries
end InitECandidate.Runtime
