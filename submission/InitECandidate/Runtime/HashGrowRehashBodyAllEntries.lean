import InitECandidate.Runtime.HashGrowRehashBody
import InitECandidate.Runtime.HashGrowRehashInsertAllEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual original rehash fragment preserves the earlier allocated region. -/
theorem evaluate_hashGrow_rehash_body_all_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count oldKeys oldValues oldOrder slot : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word oldKeys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word oldValues)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word oldOrder)))
    (orderDomain : state.memaddrs (oldOrder + count * 8))
    (slotMemory : state.memory (oldOrder + count * 8) = .word slot)
    (countLocal : state.locals.lookup (ofString "k") = some (.val (.word count)))
    (valueDomain : state.memaddrs (oldValues + slot * 8))
    (keyAligned : (oldKeys + slot * stride).toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (oldKeys + slot * stride + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (oldKeys + slot * stride + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state hashGrowRehashBody = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity (count + 1) post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.locals = (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state).locals ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word slot)) state
  have validEntry := invariant.after_read state entered table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have slotLocal : entered.locals.lookup (ofString "i") = some (.val (.word slot)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,tail,valid,entriesAfter,words,reverse,cost,remaining,locals,globals,code,addresses,endian⟩ :=
    evaluate_hashGrow_rehash_insert_all_entries entered table keys stride capacity used values order orderPos count oldKeys oldValues slot bits validEntry
      ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans keysLocal)
      ((other _ (by decide)).trans strideLocal) ((other _ (by decide)).trans valuesLocal) slotLocal
      ((other _ (by decide)).trans countLocal) valueDomain keyAligned sourceWordDomain sourceByteDomain roomAfter budget
      (entries.after_memory state entered order capacity count rfl)
      (valueEntries.after_read state entered used values capacity rfl rfl rfl)
      (reverseEntries.after_read state entered used orderPos capacity count rfl rfl rfl) keysBeforeValues
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (hashOrderAddress (ofString "order") (ofString "k"))) = some (.val (.word slot)) := by
    simp only [evalHOLExact,isWfShapeExactHOL]
    rw [eval_hashOrderAddress state (ofString "order") (ofString "k") oldOrder count orderLocal countLocal]
    simp [memLoadHOLExact]
    exact ⟨orderDomain,slotMemory⟩
  have distinct : ofString "k" ≠ ofString "i" := by decide
  have commute : (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) entered).locals =
      (setVarHOLFinite (ofString "i") (.val (.word slot))
        (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state)).locals := by
    apply HolFiniteMapExact.ext
    funext name
    by_cases first : ofString "k" = name <;> by_cases second : ofString "i" = name <;>
      simp_all [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have localShape := locals.trans commute
  have restored := restore_body_locals (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state)
    post (ofString "i") (.val (.word slot)) localShape
  have saved : (setVarHOLFinite (ofString "k") (.val (.word (count + 1))) state).locals.lookup (ofString "i") =
      state.locals.lookup (ofString "i") := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct]
  rw [saved] at restored
  rw [source_hashGrow_rehash_body,evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word slot))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
  rw [if_pos shapeOk]
  dsimp only [hashGrowRehashInsertAdvance,entered] at tail
  rw [tail]
  exact ⟨_,rfl,valid.after_read post _ table keys stride capacity used values order orderPos (count + 1) bits rfl rfl rfl rfl,
    entriesAfter.after_memory post _ order capacity (count + 1) rfl,
    words.after_read post _ used values capacity rfl rfl rfl,
    reverse.after_read post _ used orderPos capacity (count + 1) rfl rfl rfl,
    cost,remaining,restored,globals,code,addresses,endian⟩

#print axioms evaluate_hashGrow_rehash_body_all_entries
end InitECandidate.Runtime
