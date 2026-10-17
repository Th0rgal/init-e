import InitECandidate.Runtime.HashDeleteMoveArrays32
import InitECandidate.Runtime.HashDeleteValueTailOther32
import InitECandidate.Runtime.HashTableReadyIntervalFrame32
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original key/value/order movement preserves a disjoint table. -/
theorem evaluate_hashDelete_move_other32 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan values order orderPos position value used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (small : (keys + hole * stride).toNat + 32 ≤ 33806089496)
    (aligned : (keys + hole * stride).toNat % 8 = 0) (scanAligned : (keys + scan * stride).toNat % 8 = 0) (budget : 32 + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs ((keys + hole * stride) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL ((keys + hole * stride) + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs ((keys + scan * stride) + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL ((keys + scan * stride) + BitVec.ofNat 64 offset)))
    (protectedCells : ∀ cell ∈ ([values + scan * 8,orderPos + scan * 8] : List (BitVec 64)),
      ∀ offset : Nat, offset < 32 →
        cell ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
        cell ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
    (valuesLocal : state.locals.lookup (ofString "vals") = some (.val (.word values)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (reverseLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (valueDomain : state.memaddrs (values + scan * 8))
    (valueCell : state.memory (values + scan * 8) = .word value)
    (destinationDomain : state.memaddrs (values + hole * 8))
    (loadDomain : state.memaddrs (orderPos + scan * 8))
    (loadCell : state.memory (orderPos + scan * 8) = .word position)
    (separate : orderPos + scan * 8 ≠ values + hole * 8)
    (orderDomain : state.memaddrs (order + position * 8))
    (reverseDomain : state.memaddrs (orderPos + hole * 8))
    (table : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < items.toNat)
    (otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (ready : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (copyOutside : (keys + hole * stride).toNat + 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ (keys + hole * stride).toNat)
    (valuesSeparate : values.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat)
    (orderSeparate : order.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ order.toNat)
    (reverseSeparate : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ orderPos.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + 33 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have valueProtected := protectedCells (values + scan * 8) (by simp)
  obtain ⟨copied,copyRun,_,cost,remaining,globals,postCode,addresses,endian,locals,frame⟩ :=
    evaluate_hashDelete_copy_frame state keys stride hole scan 32 (values + scan * 8)
      keysLocal strideLocal holeLocal scanLocal sizeLocal small aligned scanAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain
      (fun offset inside => (valueProtected offset inside).1)
      (fun offset inside => (valueProtected offset inside).2) code
  have valueAfter : copied.memory (values + scan * 8) = .word value := by
    rw [frame _ (fun offset inside => (valueProtected offset inside).1)
      (fun offset inside => (valueProtected offset inside).2)]
    exact valueCell
  have reverseProtected := protectedCells (orderPos + scan * 8) (by simp)
  have positionAfter : copied.memory (orderPos + scan * 8) = .word position := by
    rw [frame _ (fun offset inside => (reverseProtected offset inside).1)
      (fun offset inside => (reverseProtected offset inside).2)]
    exact loadCell
  have copiedReady := ready.interval_frame state copied otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
    (by
      intro watched lower upper
      have separation := memcpy_interval_separate (keys + hole * stride) 32 watched aligned small
        (by rcases copyOutside with before | after
            · exact Or.inr (by change (keys + hole * stride).toNat + 32 ≤ watched.toNat; omega)
            · exact Or.inl (by omega))
      exact frame watched (fun offset inside => (separation offset inside).1) (fun offset inside => (separation offset inside).2))
    globals postCode addresses endian
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bound := invariant.endBound
  have room := invariant.room
  obtain ⟨post,tail,preserved,ticks,postGlobals,postCodeEq,postDomain,postEndian⟩ := evaluate_hashDelete_value_tail_other copied values order orderPos hole scan position value
    (by rw [locals]; exact valuesLocal) (by rw [locals]; exact orderLocal)
    (by rw [locals]; exact reverseLocal) (by rw [locals]; exact holeLocal) (by rw [locals]; exact scanLocal)
    (by rw [addresses]; exact valueDomain) valueAfter (by rw [addresses]; exact destinationDomain)
    (by rw [addresses]; exact loadDomain) positionAfter separate
    (by rw [addresses]; exact orderDomain) (by rw [addresses]; exact reverseDomain)
    capacity holeInside (by omega) invariant.valuesAligned invariant.orderAligned invariant.orderPosAligned
    (by omega) (by omega) bound otherTable pointer otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
    copiedReady valuesSeparate orderSeparate reverseSeparate
  change state.clock ≤ copied.clock + 32 + 1 at cost
  exact ⟨post,copyRun.trans tail,preserved,by omega,by omega,
    postGlobals.trans globals,postCodeEq.trans postCode,postDomain.trans addresses,postEndian.trans endian⟩

#print axioms evaluate_hashDelete_move_other32
end InitECandidate.Runtime
