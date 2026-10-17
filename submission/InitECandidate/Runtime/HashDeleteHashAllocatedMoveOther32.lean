import InitECandidate.Runtime.HashDeleteHashAllocatedMove32
import InitECandidate.Runtime.HashDeleteMoveScopedOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Hash call and moving branch preserve disjoint ready tables. -/
theorem evaluate_hashDelete_hash_allocated_move_other32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan values order orderPos used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (capacityLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (scanInside : scan.toNat < capacity.toNat)
    (occupied : hashOccupancyRead state used scan ≠ some 0)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (budget : 34 ≤ state.clock)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (orderEntries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (valueEntries : HashValueEntriesWord used values capacity state)
    (otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨
      otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ hash : BitVec 64, hashDeleteMoveRequired hole scan (hash &&& (capacity - 1)) →
    ∃ post, evaluateHOLFiniteState state hashDeleteLoopRest = (none,post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + 34 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨aligned,words,_,_⟩ := invariant.key_slot_domains state table keys stride capacity used values order orderPos items scan bits scanInside
  have hashDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (keys + scan * stride + BitVec.ofNat 64 offset) := by
    intro offset member
    apply words
    simp at member
    omega
  obtain ⟨hash,hashed,ticks,memory,globals,code,domain,endian,locals,hashRun⟩ :=
    evaluate_hashDelete_hash32 state keys scan stride keysLocal scanLocal strideLocal sizeLocal invariant.code (by omega) aligned hashDomain
  refine ⟨hash,?_⟩
  intro moves
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) hashed
  have other : ∀ name, name ≠ ofString "h" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have h : entered.locals.lookup (ofString "h") = some (.val (.word hash)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have reads : hashOccupancyRead entered used = hashOccupancyRead state used := by
    funext slot
    unfold hashOccupancyRead
    rw [show entered.memory = state.memory from memory,show entered.memaddrs = state.memaddrs from domain,show entered.be = state.be from endian]
  have enteredInvariant := invariant.after_read state entered table keys stride capacity used values order orderPos items bits memory code domain endian
  have clock : entered.clock = state.clock - 1 := ticks
  have enteredReady := ready.after_read state entered otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer memory globals code domain endian
  obtain ⟨post,run,preserved,cost,remaining,postGlobals,postCode,postDomain,postEndian⟩ :=
    evaluate_hashDelete_move_scoped_other32 entered keys stride hole scan values order orderPos used capacity items
      ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
      ((other _ (by decide)).trans holeLocal) ((other _ (by decide)).trans scanLocal)
      ((other _ (by decide)).trans sizeLocal) hash h ((other _ (by decide)).trans capacityLocal) moves table bits
      enteredInvariant scanInside (by rw [reads]; exact occupied) keysBeforeValues (by omega)
      ((other _ (by decide)).trans valuesLocal) ((other _ (by decide)).trans orderLocal) ((other _ (by decide)).trans reverseLocal)
      (entries.after_read state entered used orderPos capacity items memory domain endian)
      (orderEntries.after_memory state entered order capacity items memory) holeInside
      (valueEntries.after_read state entered used values capacity memory domain endian)
      otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits enteredReady separated
  rw [hashRun]
  change ∃ post, (let output := evaluateHOLFiniteState entered hashDeleteAfterHash; _) = _ ∧ _
  rw [run]
  refine ⟨_,rfl,preserved.after_read post _ otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,
    ?_,?_,postGlobals.trans globals,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · change state.clock ≤ post.clock + 34
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms evaluate_hashDelete_hash_allocated_move_other32
end InitECandidate.Runtime
