import InitECandidate.Runtime.HashInsertIndexMemory
import InitECandidate.Runtime.HashInsertProbeArraysEntries
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashInsert_index_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count hash keys stride key keyLength : BitVec 64) (bits : Nat)
    (power : capacity.toNat = 2 ^ bits) (code : state.code = originalRuntimeCode)
    (hashLocal : state.locals.lookup (ofString "h") = some (.val (.word hash)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (budget : capacity.toNat + keyLength.toNat + 1 ≤ state.clock)
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (environment : HashInsertSlotEnvironment capacity used table values value order orderPos count state)
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ keys.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496) (fits : keyLength.toNat ≤ stride.toNat)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (entries : HashOrderEntriesBound order capacity count state)
    (valuesAligned : values.toNat % 8 = 0) (orderAligned : order.toNat % 8 = 0)
    (reverseAligned : orderPos.toNat % 8 = 0)
    (headerOrder : table.toNat + 72 ≤ order.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (bounded : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (countRoom : count.toNat < capacity.toNat) :
    ∃ post, evaluateHOLFiniteState state hashInsertIndexScope =
        (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 1 ∧ post.clock ≤ state.clock := by
  let index := hashFindInitialIndex hash capacity
  let entered := setVarHOLFinite (ofString "i") (.val (.word index)) state
  have other : ∀ name, name ≠ ofString "i" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have i : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have invariant := HashInsertSlotEnvironment.bind_index capacity used table values value order orderPos count index state environment
  obtain ⟨post,run,valid,header,agreement,cost,remaining⟩ := evaluate_hashInsert_probe_arrays_entries entered capacity used table values value
    order orderPos count index keys stride key keyLength bits power code i
    (by rw [other _ (by decide)]; exact capacityLocal) (by rw [other _ (by decide)]; exact usedLocal)
    (by rw [other _ (by decide)]; exact keysLocal) (by rw [other _ (by decide)]; exact strideLocal)
    (by rw [other _ (by decide)]; exact keyLocal) (by rw [other _ (by decide)]; exact lengthLocal)
    (hashFind_initial_index_bound hash capacity bits power).2 budget readable room invariant keysAligned strideAligned keyAligned usedAligned
    headerBefore keysBefore usedBound fits arrayDomain sourceWordDomain sourceByteDomain
    (entries.after_memory state entered order capacity count rfl) valuesAligned orderAligned reverseAligned
    headerOrder valuesBefore usedBefore orderBefore bounded countRoom
  unfold hashInsertIndexScope
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [eval_hashFind_initial_index state hash capacity hashLocal capacityLocal]
  dsimp only
  have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word index))) = true := by simp [shapeOfHOLExact,shapeEqHOL]
  rw [if_pos shapeOk,run]
  exact ⟨_,rfl,valid.after_memory post _ order capacity (count + 1) rfl,header,agreement,cost,remaining⟩

#print axioms evaluate_hashInsert_index_entries
end InitECandidate.Runtime
