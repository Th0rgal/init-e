import InitECandidate.Runtime.HashDeleteNoMove
import InitECandidate.Runtime.HashDeleteMoveScoped32
import InitECandidate.Runtime.HashDeleteHash32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_hash_allocated32 {F : Type} (state : PanSemStateFiniteExact 64 F)
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
 :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoopRest = (none,post) ∧
      state.clock ≤ post.clock + 34 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HashReverseEntriesBound used orderPos capacity items post ∧ HashOrderEntriesBound order capacity items post ∧
      (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
        hashOccupancyRead post used slot = hashOccupancyRead state used slot) ∧
      (post.locals.lookup (ofString "i") = some (.val (.word hole)) ∨ post.locals.lookup (ofString "i") = some (.val (.word scan))) ∧ HashValueEntriesWord used values capacity post ∧ post.locals.lookup (ofString "j") = some (.val (.word scan)) := by
  obtain ⟨aligned,words,_,_⟩ := invariant.key_slot_domains state table keys stride capacity used values order orderPos items scan bits scanInside
  have hashDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (keys + scan * stride + BitVec.ofNat 64 offset) := by
    intro offset member
    apply words
    simp at member
    omega
  obtain ⟨hash,ready,ticks,memory,globals,code,domain,endian,locals,hashRun⟩ :=
    evaluate_hashDelete_hash32 state keys scan stride keysLocal scanLocal strideLocal sizeLocal invariant.code (by omega) aligned hashDomain
  let entered := setVarHOLFinite (ofString "h") (.val (.word hash)) ready
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
  classical
  by_cases moves : hashDeleteMoveRequired hole scan (hash &&& (capacity - 1))
  · obtain ⟨post,run,cost,remaining,postGlobals,postCode,postDomain,postEndian,reverse,ordered,occupancy,holePost,valuePost,scanPost⟩ :=
      evaluate_hashDelete_move_scoped32 entered keys stride hole scan values order orderPos used capacity items
        ((other _ (by decide)).trans keysLocal) ((other _ (by decide)).trans strideLocal)
        ((other _ (by decide)).trans holeLocal) ((other _ (by decide)).trans scanLocal)
        ((other _ (by decide)).trans sizeLocal) hash h ((other _ (by decide)).trans capacityLocal) moves table bits
        enteredInvariant scanInside (by rw [reads]; exact occupied) keysBeforeValues (by omega)
        ((other _ (by decide)).trans valuesLocal) ((other _ (by decide)).trans orderLocal) ((other _ (by decide)).trans reverseLocal)
        (entries.after_read state entered used orderPos capacity items memory domain endian)
        (orderEntries.after_memory state entered order capacity items memory) holeInside
        (valueEntries.after_read state entered used values capacity memory domain endian)
    rw [hashRun]
    change ∃ post, (let output := evaluateHOLFiniteState entered hashDeleteAfterHash; _) = _ ∧ _
    rw [run]
    refine ⟨_,rfl,?_,?_,postGlobals.trans globals,postCode.trans code,postDomain.trans domain,postEndian.trans endian,
      reverse.after_read post _ used orderPos capacity items rfl rfl rfl,
      ordered.after_memory post _ order capacity items rfl,?_,?_,valuePost.after_read post _ used values capacity rfl rfl rfl,?_⟩
    · change state.clock ≤ post.clock + 34
      change entered.clock ≤ post.clock + 32 + 1 at cost
      omega
    · change post.clock ≤ state.clock; omega
    · intro slot inside
      exact (occupancy slot inside).trans (congrFun reads slot)
    · right
      change (HolFiniteMapExact.resVarEq post.locals (ofString "h",state.locals.lookup (ofString "h"))).lookup (ofString "i") = _
      rw [restore_other_local _ _ (ofString "i") _ (by decide)]
      exact holePost
    · change (HolFiniteMapExact.resVarEq post.locals (ofString "h",state.locals.lookup (ofString "h"))).lookup (ofString "j") = _
      rw [restore_other_local _ _ (ofString "j") _ (by decide)]
      exact scanPost
  · have noMove := evaluate_hashDelete_no_move entered hole scan hash capacity
      ((other _ (by decide)).trans holeLocal) ((other _ (by decide)).trans scanLocal) h
      ((other _ (by decide)).trans capacityLocal) moves
    rw [hashRun]
    change ∃ post, (let output := evaluateHOLFiniteState entered hashDeleteAfterHash; _) = _ ∧ _
    rw [noMove]
    refine ⟨_,rfl,?_,?_,globals,code,domain,endian,
      entries.after_read state _ used orderPos capacity items memory domain endian,
      orderEntries.after_memory state _ order capacity items memory,?_,?_,
      valueEntries.after_read state _ used values capacity memory domain endian,?_⟩
    · change state.clock ≤ entered.clock + 34; omega
    · change entered.clock ≤ state.clock; omega
    · intro slot inside
      exact congrFun reads slot
    · left
      change (HolFiniteMapExact.resVarEq entered.locals (ofString "h",state.locals.lookup (ofString "h"))).lookup (ofString "i") = _
      rw [restore_other_local _ _ (ofString "i") _ (by decide)]
      exact (other _ (by decide)).trans holeLocal
    · change (HolFiniteMapExact.resVarEq entered.locals (ofString "h",state.locals.lookup (ofString "h"))).lookup (ofString "j") = _
      rw [restore_other_local _ _ (ofString "j") _ (by decide)]
      exact (other _ (by decide)).trans scanLocal

#print axioms evaluate_hashDelete_hash_allocated32
end InitECandidate.Runtime
