import InitECandidate.Runtime.HashInsertProbeEntries32
import InitECandidate.Runtime.HashInsertIndexEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Index initialization and scope restoration preserve the insertion guarantees. -/
theorem evaluate_hashInsert_index_entries32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count hash keys stride key : BitVec 64) (bits : Nat)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (budget : capacity.toNat + (32 : BitVec 64).toNat + 1 ≤ state.clock)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (sourceAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (entries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (orderEntries : HashOrderEntriesBound order capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertIndexScope =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + 33 ∧ post.clock ≤ state.clock ∧
      HashValueEntriesWord used values capacity post ∧
      HashReverseEntriesBound used orderPos capacity (count + 1) post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let index := hashFindInitialIndex hash capacity
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have i : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredInvariant := invariant.after_read state entered table keys stride capacity used values order orderPos count bits rfl rfl rfl rfl
  obtain ⟨post,run,header,agreement,cost,remaining,words,reverse,ordered,globals,code,domain,endian⟩ :=
    evaluate_hashInsert_probe_entries32 entered capacity used table values value order orderPos count index keys stride key bits
      ((other _ (by decide)).trans tableLocal) ((other _ (by decide)).trans orderLocal)
      ((other _ (by decide)).trans orderPosLocal) ((other _ (by decide)).trans valueLocal)
      i ((other _ (by decide)).trans capacityLocal) ((other _ (by decide)).trans usedLocal)
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans lengthLocal)
      (hashFind_initial_index_bound hash capacity bits invariant.power).2 budget enteredInvariant sourceAligned
      sourceWordDomain sourceByteDomain keysBeforeValues
      (entries.after_read state entered used values capacity rfl rfl rfl)
      (reverseEntries.after_read state entered used orderPos capacity count rfl rfl rfl)
      (orderEntries.after_memory state entered order capacity count rfl)
  unfold hashInsertIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capacityLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word index))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos shapeOk,run]
  refine ⟨_,rfl,header,agreement,cost,remaining,?_,?_,?_,globals,code,domain,endian⟩
  · exact words.after_read post _ used values capacity rfl rfl rfl
  · exact reverse.after_read post _ used orderPos capacity (count + 1) rfl rfl rfl
  · exact ordered.after_memory post _ order capacity (count + 1) rfl

#print axioms evaluate_hashInsert_index_entries32
end InitECandidate.Runtime
