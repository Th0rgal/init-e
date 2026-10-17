import InitECandidate.Runtime.HashDeleteFinalStoresJournal
import InitECandidate.Runtime.JournalUndoRecordsRead
import InitECandidate.Runtime.HashTableReady
import InitECandidate.Runtime.HashTableSetExistingLinkedWidth
import InitECandidate.Runtime.HashTableReadyWordOutside
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original existing-key update preserves both tables when its value
array is disjoint from the other table's allocation, including relocated arrays. -/
theorem HashTableReady.set_existing_with_record_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items index value : BitVec 64) (bits : Nat)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat) (missing : ProgHOL 64)
    (journal : BitVec 64) (journalCount : Nat)
    (journalBound : journal.toNat + journalCount * 32 ≤ 33806089496)
    (separate : values.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + journalCount * 32 ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state (hashSetExistingTail missing) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
      (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) ∧
      post.clock = state.clock ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,valid,words,reverse,ordered,clock,globals,code,domain,endian,linked⟩ :=
    ready.live.arrays.set_existing_tail_linked_width state keyLength table keys stride capacity used values order orderPos items index value bits
      t i v inside missing ready.valuesWord ready.reverse ready.live.entries ready.linked
  have facts := ready.live.arrays.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  have checked := evaluate_hashSet_existing_tail state table index capacity values value missing
    (by intro equal; rw [equal] at inside; omega) t i v
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 16 (by decide)) ready.live.arrays.cell16
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 40 (by decide)) ready.live.arrays.cell40 (facts.valueDomain index inside)
  have same : post = emptyLocalsHOLFinite (sourceWriteWord state (values + index * 8) value) := congrArg Prod.snd (run.symm.trans checked)
  have vu := ready.live.arrays.valuesBefore
  have uo := ready.live.arrays.usedBefore
  have oo := ready.live.arrays.orderBefore
  have bounded := ready.live.arrays.endBound
  have address := (hashFind_slot_address values index 8 capacity inside (by change values.toNat + capacity.toNat * 8 ≤ 33806089496; omega)
    ready.live.arrays.valuesAligned (by decide)).1
  change (values + index * 8).toNat = values.toNat + index.toNat * 8 at address
  have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
  have outside : (values + index * 8).toNat < journal.toNat ∨ journal.toNat + journalCount * 32 ≤ (values + index * 8).toNat := by
    rcases separate with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by omega)
  have otherPost : (∀ index : Nat, index < journalCount → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset)) := by
    intro record insideRecord offset member
    have smallOffset : offset < 32 := by simp at member; omega
    have interval := journal_undo_field_interval journal journalCount record offset journalBound insideRecord smallOffset
    have different : journal + BitVec.ofNat 64 record * 32 + BitVec.ofNat 64 offset ≠ values + index * 8 := by
      intro equal
      rw [equal] at interval
      rcases outside with before | after <;> omega
    rw [same]
    change (sourceWriteWord state (values + index * 8) value).memory _ = _
    simp only [sourceWriteWord]
    simp
    intro equal
    exact False.elim (different equal)
  exact ⟨post,run,⟨⟨valid,ordered,ready.live.frontier.after_globals state post orderPos capacity pointer globals⟩,words,reverse,linked,ready.ordering⟩,
    otherPost,clock,globals,code,domain,endian⟩

#print axioms HashTableReady.set_existing_with_record_frame
end InitECandidate.Runtime
