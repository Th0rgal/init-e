import InitECandidate.Runtime.HashTableValuesInSetMissing
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
import InitECandidate.Runtime.HashInsertCopyMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderedMemoryKU
import InitECandidate.Runtime.HashInsertProbeMemoryKU
import InitECandidate.Runtime.HashInsertCopyBoundsKU
import InitECandidate.Runtime.HashInsertProbeArraysMemoryKU
import InitECandidate.Runtime.HashInsertIndexMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderEntriesKU
import InitECandidate.Runtime.HashInsertCopyOrderedEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesKU
import InitECandidate.Runtime.HashInsertCopyEntriesWidthKU
import InitECandidate.Runtime.HashInsertProbeEntriesWidthKU
import InitECandidate.Runtime.HashInsertIndexEntriesWidthKU
import InitECandidate.Runtime.HashInsertHashAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertBodyAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCopyLinkedWidthKU
import InitECandidate.Runtime.HashInsertProbeLinkedWidthKU
import InitECandidate.Runtime.HashInsertIndexLinkedWidthKU
import InitECandidate.Runtime.HashInsertHashLinkedSupportedKU
import InitECandidate.Runtime.HashInsertBodyLinkedSupportedKU
import InitECandidate.Runtime.HashInsertHashMemorySupportedKU
import InitECandidate.Runtime.HashInsertBodyMemorySupportedKU
import InitECandidate.Runtime.HashInsertCallAllEntriesSupportedKU
import InitECandidate.Runtime.HashInsertCallLinkedSupportedKU
import InitECandidate.Runtime.HashInsertCallMemorySupportedKU
import InitECandidate.Runtime.HashTableArraysFrameSupportedKU
import InitECandidate.Runtime.HashTableArraysAllEntriesSupportedKU
import InitECandidate.Runtime.HashTableArraysLinkedInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertSupportedKU
import InitECandidate.Runtime.HashTableReadyInsertPhysicalFrameSupportedKU
import InitECandidate.Runtime.HashTableValuesInInsertCopyKU
import InitECandidate.Runtime.HashTableValuesInInsertProbeKU
import InitECandidate.Runtime.HashTableValuesInInsertCallKU
import InitECandidate.Runtime.HashTableValuesInReadyUpdatesKU
/-! Unaligned-key copy of `HashTableValuesInSetMissing` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual missing-key set branch retains registered occupied values when
the load factor permits insertion without growth, including its final return. -/
theorem HashTableReady.set_missing_values_in_no_growthKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (items.toNat + 1) * 2 ≤ capacity.toNat) (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets)
 :
    ∃ post, evaluateHOLFiniteState state hashSetMissing = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos (items + 1) bits pointer post ∧
      HashTableValuesIn table targets post ∧
      (∀ address : BitVec 64, ¬tablePhysicalRegion table keys stride capacity used values order orderPos address →
        post.memory address = state.memory address) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have condition := eval_hashSet_growth_false state table capacity items t
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 16 (by decide)) ready.live.arrays.cell16
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 24 (by decide)) ready.live.arrays.cell24 loadFactor
  have selected : evaluateHOLFiniteState state
      (.ite hashSetGrowthCondition (.call (some (none,none)) (ofString "htab_grow") [.var .local (ofString "t")]) .skip) = (none,state) := by
    rw [evaluateHOLFiniteState_ite,condition]
    simp [evaluateHOLFiniteState_skip]
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word key),.val (.word value)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,k,v]
  obtain ⟨post,insert,valid,registered,otherValid,cost,remaining,_,globals,domain,endian⟩ :=
    ready.insert_supported_values_in_frameKU state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
      (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value")) arguments
      keyAligned len8 keyFit sourceWordDomain sourceByteDomain (by omega) budget targets entries member
  have returned : evaluateHOLFiniteState post (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite post,?_,
    valid.after_read post _ keyLength table keys stride capacity used values order orderPos (items + 1) bits pointer rfl rfl rfl rfl rfl,
    registered.after_read rfl rfl rfl,otherValid,
    cost,remaining,globals,valid.live.arrays.code.trans ready.live.arrays.code.symm,domain,endian⟩
  rw [source_hashSet_missing]
  exact evaluate_seq_none selected (evaluate_seq_none insert returned)

#print axioms HashTableReady.set_missing_values_in_no_growthKU
end InitECandidate.Runtime
