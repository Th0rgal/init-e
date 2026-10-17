import InitECandidate.Runtime.HashDeleteOccupiedIterationSupported
import InitECandidate.Runtime.HashDeleteHashAllocatedOtherSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Advancing and processing an occupied deletion slot preserves other tables. -/
theorem evaluate_hashDelete_occupied_iteration_other_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength keys stride hole index values order orderPos used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (indexLocal : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (table : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (indexInside : (hashProbeNext index capacity).toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used (hashProbeNext index capacity) ≠ some 0)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (budget : keyLength.toNat + 2 ≤ state.clock)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (orderEntries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoopBody = (none,post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + keyLength.toNat + 2 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let next := hashProbeNext index capacity
  let advanced := setVarHOLFinite (ofString "j") (.val (.word next)) state
  have other : ∀ name, name ≠ ofString "j" → advanced.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have j : advanced.locals.lookup (ofString "j") = some (.val (.word next)) := by
    simp [advanced,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos items bits
  obtain ⟨byte,loaded⟩ : ∃ byte, hashOccupancyRead state used next = some byte := by
    have available := facts.byteDomain next indexInside
    unfold hashOccupancyRead panMemLoadByteHOL
    dsimp only
    rw [if_pos available]
    exact ⟨_,rfl⟩
  have nonzero : byte ≠ 0 := by
    intro same
    apply occupied
    simpa [same] using loaded
  have selected := evaluate_hashDelete_occupied_iteration state index capacity used byte indexLocal capacityLocal usedLocal loaded nonzero
  have advancedInvariant := invariant.after_read state advanced keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl
  have advancedReady := ready.after_read state advanced otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl
  obtain ⟨post,run,preserved,cost,remaining,globals,code,domain,endian⟩ :=
    evaluate_hashDelete_hash_allocated_other_supported advanced keyLength keys stride hole next values order orderPos used capacity items
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans holeLocal) j ((other _ (by decide)).trans sizeLocal)
      ((other _ (by decide)).trans capacityLocal) table bits supported advancedInvariant indexInside occupied keysBeforeValues budget
      ((other _ (by decide)).trans valuesLocal) ((other _ (by decide)).trans orderLocal) ((other _ (by decide)).trans reverseLocal)
      (entries.after_read state advanced used orderPos capacity items rfl rfl rfl)
      (orderEntries.after_memory state advanced order capacity items rfl) holeInside
      (valueEntries.after_read state advanced used values capacity rfl rfl rfl)
      otherKeyLength otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits advancedReady separated
  exact ⟨post,selected.trans run,preserved,cost,remaining,globals,code,domain,endian⟩

#print axioms evaluate_hashDelete_occupied_iteration_other_supported
end InitECandidate.Runtime
