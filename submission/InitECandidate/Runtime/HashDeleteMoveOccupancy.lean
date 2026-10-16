import InitECandidate.Runtime.HashDeleteCopyFrame
import InitECandidate.Runtime.HashOccupancyPreservation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_move_occupancy {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan size values order orderPos position value capacity used : BitVec 64)
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (holeLocal : state.locals.lookup (ofString "i") = some (.val (.word hole)))
    (scanLocal : state.locals.lookup (ofString "j") = some (.val (.word scan)))
    (sizeLocal : state.locals.lookup (ofString "klen") = some (.val (.word size)))
    (small : (keys + hole * stride).toNat + size.toNat ≤ 33806089496)
    (aligned : (keys + hole * stride).toNat % 8 = 0) (scanAligned : (keys + scan * stride).toNat % 8 = 0) (budget : size.toNat + 1 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs ((keys + hole * stride) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL ((keys + hole * stride) + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs ((keys + scan * stride) + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < size.toNat → state.memaddrs (panByteAlignHOL ((keys + scan * stride) + BitVec.ofNat 64 offset)))
    (protectedCells : ∀ cell ∈ ([values + scan * 8,orderPos + scan * 8] : List (BitVec 64)),
      ∀ offset : Nat, offset < size.toNat →
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
    (copyOccupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      ∀ offset : Nat, offset < size.toNat →
        panByteAlignHOL (used + slot) ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
        panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (storeOccupancySeparate : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8 ∧
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
        hashOccupancyRead post used slot = hashOccupancyRead state used slot) ∧
      post.locals = (setVarHOLFinite (ofString "i") (.val (.word scan)) state).locals := by
  have valueProtected := protectedCells (values + scan * 8) (by simp)
  obtain ⟨copied,copyRun,_,cost,remaining,globals,postCode,addresses,endian,locals,frame⟩ :=
    evaluate_hashDelete_copy_frame state keys stride hole scan size (values + scan * 8)
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
  rw [copyRun,tail]
  refine ⟨_,rfl,cost,remaining,globals,postCode,addresses,endian,?_,?_⟩
  · intro slot inside
    have disjoint := storeOccupancySeparate slot inside
    have sv : panByteAlignHOL (used + slot) ≠ values + hole * 8#64 := disjoint.1
    have so : panByteAlignHOL (used + slot) ≠ order + position * 8#64 := disjoint.2.1
    have sr : panByteAlignHOL (used + slot) ≠ orderPos + hole * 8#64 := disjoint.2.2
    have copiedCell := frame (panByteAlignHOL (used + slot))
      (fun offset bound => (copyOccupancySeparate slot inside offset bound).1)
      (fun offset bound => (copyOccupancySeparate slot inside offset bound).2)
    simp [hashOccupancyRead,panMemLoadByteHOL,sourceWriteWord,setVarHOLFinite,sv,so,sr,
      addresses,endian,copiedCell]
    cases state
    cases copied
    dsimp only at *
    subst_vars
    rfl
  · change HolFiniteMapExact.resVarEq
      ((copied.locals.update (ofString "moved_pos",.val (.word position))).update
        (ofString "i",.val (.word scan)))
      (ofString "moved_pos",copied.locals.lookup (ofString "moved_pos")) =
        state.locals.update (ofString "i",.val (.word scan))
    rw [locals]
    apply HolFiniteMapExact.ext
    funext name
    have distinct : ofString "moved_pos" ≠ ofString "i" := by decide
    by_cases atTemporary : name = ofString "moved_pos"
    · subst name
      cases saved : state.locals.lookup (ofString "moved_pos") <;>
        simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
          HolFiniteMapExact.lookup_eraseEq,HolFiniteMapExact.lookup_update,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,distinct,Ne.symm distinct,saved]
    · by_cases atHole : name = ofString "i"
      · subst name
        cases saved : state.locals.lookup (ofString "moved_pos") <;>
          simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
            HolFiniteMapExact.lookup_eraseEq,HolFiniteMapExact.lookup_update,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,distinct,Ne.symm distinct,saved]
      · cases saved : state.locals.lookup (ofString "moved_pos") <;>
          simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
            HolFiniteMapExact.lookup_eraseEq,HolFiniteMapExact.lookup_update,FUPDATE,FUPDATE_HOL,FDOMSUB_HOL,atTemporary,atHole,
            Ne.symm atTemporary,Ne.symm atHole,saved]

#print axioms evaluate_hashDelete_move_occupancy
end InitECandidate.Runtime
