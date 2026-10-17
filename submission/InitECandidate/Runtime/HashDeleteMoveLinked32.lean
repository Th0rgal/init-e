import InitECandidate.Runtime.HashDeleteMoveWords
import InitECandidate.Runtime.HashTableArraysCopyFrame32
import InitECandidate.Runtime.HashDeleteOrderLinkedStores32
import InitECandidate.Runtime.HashDeleteOrderLinkedCopy32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_move_linked32 {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (holeInside : hole.toNat < capacity.toNat) (scanInside : scan.toNat < capacity.toNat)
    (deletedPosition : BitVec 64) (different : scan ≠ hole)
    (occupied : hashOccupancyRead state used scan ≠ some 0)
    (linked : HashDeleteOrderLinked used order orderPos capacity items hole deletedPosition state) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      state.clock ≤ post.clock + 33 ∧ post.clock ≤ state.clock ∧
      HashDeleteOrderLinked used order orderPos capacity items scan deletedPosition post := by
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
  have tail := evaluate_hashDelete_value_tail copied values order orderPos hole scan position value
    (by rw [locals]; exact valuesLocal) (by rw [locals]; exact orderLocal)
    (by rw [locals]; exact reverseLocal) (by rw [locals]; exact holeLocal) (by rw [locals]; exact scanLocal)
    (by rw [addresses]; exact valueDomain) valueAfter (by rw [addresses]; exact destinationDomain)
    (by rw [addresses]; exact loadDomain) positionAfter separate
    (by rw [addresses]; exact orderDomain) (by rw [addresses]; exact reverseDomain)
  have copiedInvariant := invariant.key_copy_frame state copied table keys stride capacity used values order orderPos items hole bits
    holeInside postCode addresses endian frame
  have copiedLinked := linked.copy_frame_layout32 state copied table keys stride capacity used values order orderPos items hole hole deletedPosition bits
    invariant holeInside addresses endian frame
  have occupancy := (invariant.delete_occupancy_separate state table keys stride capacity used values order orderPos items hole hole bits holeInside holeInside).1
  have cellFrame := frame (panByteAlignHOL (used + scan))
    (fun offset small => (occupancy scan scanInside offset small).1)
    (fun offset small => (occupancy scan scanInside offset small).2)
  have reads : hashOccupancyRead copied used scan = hashOccupancyRead state used scan := by
    cases state
    cases copied
    dsimp only at *
    subst_vars
    simp [hashOccupancyRead,panMemLoadByteHOL,cellFrame]
  have valid := copiedLinked.move_stores_layout32 copied table keys stride capacity used values order orderPos items hole scan deletedPosition position value bits
    copiedInvariant holeInside scanInside different (by rw [reads]; exact occupied) positionAfter
  rw [copyRun,tail]
  exact ⟨_,rfl,cost,remaining,by
    apply valid.framed _ _ used order orderPos capacity items scan deletedPosition
    · intro slot inside notHole live; exact live
    · intro slot inside notHole; rfl
    · intro index inside notDeleted; rfl⟩

#print axioms evaluate_hashDelete_move_linked32
end InitECandidate.Runtime
