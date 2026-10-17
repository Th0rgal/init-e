import InitECandidate.Runtime.HashTableValuesInMoveStores
import InitECandidate.Runtime.HashTableValuesInCopyFrame
import InitECandidate.Runtime.HashDeleteMoveWords
import InitECandidate.Runtime.HashTableArraysCopyFrameWidth
import InitECandidate.Runtime.HashTableArraysMoveStoresWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_move_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength keys stride hole scan values order orderPos position value used capacity items : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (small : (keys + hole * stride).toNat + keyLength.toNat ≤ 33806089496)
    (aligned : (keys + hole * stride).toNat % 8 = 0) (scanAligned : (keys + scan * stride).toNat % 8 = 0) (budget : keyLength.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs ((keys + hole * stride) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL ((keys + hole * stride) + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs ((keys + scan * stride) + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL ((keys + scan * stride) + BitVec.ofNat 64 offset)))
    (protectedCells : ∀ cell ∈ ([values + scan * 8,orderPos + scan * 8] : List (BitVec 64)),
      ∀ offset : Nat, offset < keyLength.toNat →
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
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits state)
    (holeInside : hole.toNat < capacity.toNat) (positionBound : position.toNat < items.toNat)
    (targets : Set (BitVec 64)) (registered : HashTableValuesIn table targets state)
    (scanInside : scan.toNat < capacity.toNat) (occupied : hashOccupancyRead state used scan ≠ some 0)
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos items bits post ∧
      HashTableValuesIn table targets post ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have valueProtected := protectedCells (values + scan * 8) (by simp)
  obtain ⟨copied,copyRun,_,cost,remaining,globals,postCode,addresses,endian,locals,frame⟩ :=
    evaluate_hashDelete_copy_frame state keys stride hole scan keyLength (values + scan * 8)
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
  have tail := evaluate_hashDelete_value_tail copied values order orderPos hole scan position value
    (by rw [locals]; exact valuesLocal) (by rw [locals]; exact orderLocal)
    (by rw [locals]; exact reverseLocal) (by rw [locals]; exact holeLocal) (by rw [locals]; exact scanLocal)
    (by rw [addresses]; exact valueDomain) valueAfter (by rw [addresses]; exact destinationDomain)
    (by rw [addresses]; exact loadDomain) positionAfter separate
    (by rw [addresses]; exact orderDomain) (by rw [addresses]; exact reverseDomain)
  have copiedInvariant := invariant.key_copy_frame_width state copied keyLength table keys stride capacity used values order orderPos items hole bits
    holeInside postCode addresses endian frame
  have valid := copiedInvariant.move_stores_width copied keyLength table keys stride capacity used values order orderPos items hole position value bits holeInside positionBound
  have copiedRegistered := registered.key_copy_frame state copied keyLength table keys stride capacity used values order orderPos items hole bits invariant targets holeInside keysBeforeValues addresses endian frame
  have valueMember := registered capacity used values invariant.cell16 invariant.cell48 invariant.cell40 scan scanInside occupied value valueCell
  have finalRegistered := copiedRegistered.move_stores copied keyLength table keys stride capacity used values order orderPos items hole position value bits copiedInvariant targets valueMember holeInside positionBound
  rw [copyRun,tail]
  exact ⟨_,rfl,cost,remaining,valid.after_read _ _ keyLength table keys stride capacity used values order orderPos items bits rfl rfl rfl rfl,finalRegistered.after_read rfl rfl rfl,globals,postCode,addresses,endian⟩

#print axioms evaluate_hashDelete_move_values_in
end InitECandidate.Runtime
