import InitECandidate.Runtime.JournalUndoRecordsRead
import InitECandidate.Runtime.HashTableReadyInsertRecordFrameSupported
import InitECandidate.Runtime.HashSetGrowthGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original missing-key set suffix without growth preserves an earlier live
table and the inserted table, including all entry and linkage facts. -/
theorem HashTableReady.set_missing_supported_with_record_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (k : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (loadFactor : (items.toNat + 1) * 2 ≤ capacity.toNat) (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock)
    (journal : BitVec 64) (journalCount : Nat)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (beforeKeys : journal.toNat + journalCount * 32 ≤ keys.toNat)
    (beforeValues : journal.toNat + journalCount * 32 ≤ values.toNat)
    (separateHeader : journal.toNat + journalCount * 32 ≤ table.toNat ∨ table.toNat + 72 ≤ journal.toNat) :
    ∃ post, evaluateHOLFiniteState state hashSetMissing = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos (items + 1) bits pointer post ∧
      (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
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
  obtain ⟨post,insert,valid,otherValid,cost,remaining,_,globals,domain,endian⟩ :=
    ready.insert_supported_with_record_frame state keyLength table pointer keys stride capacity used values order orderPos items key value bits supported
      (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value")) arguments
      keyAligned sourceWordDomain sourceByteDomain (by omega) budget
      journal journalCount journalBound beforeKeys beforeValues separateHeader
  have returned : evaluateHOLFiniteState post (.return (.const 0)) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  refine ⟨emptyLocalsHOLFinite post,?_,
    valid.after_read post _ keyLength table keys stride capacity used values order orderPos (items + 1) bits pointer rfl rfl rfl rfl rfl,
    otherValid,
    cost,remaining,globals,valid.live.arrays.code.trans ready.live.arrays.code.symm,domain,endian⟩
  rw [source_hashSet_missing]
  exact evaluate_seq_none selected (evaluate_seq_none insert returned)

#print axioms HashTableReady.set_missing_supported_with_record_frame
end InitECandidate.Runtime
