import InitECandidate.Runtime.HashDeleteMoveReverse
import InitECandidate.Runtime.HashDeleteMoveOrder
import InitECandidate.Runtime.HashDeleteMoveOccupancy
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_hashDelete_move_invariants {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keys stride hole scan size values order orderPos position value used capacity items : BitVec 64)
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
    (entries : HashReverseEntriesBound used orderPos capacity items state)
    (positionBound : position.toNat < items.toNat)
    (copyOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      panByteAlignHOL (used + slot) ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      panByteAlignHOL (used + slot) ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (copyReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < size.toNat →
      orderPos + slot * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      orderPos + slot * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (valueOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ values + hole * 8)
    (valueReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      orderPos + slot * 8 ≠ values + hole * 8)
    (storeOccupancy : ∀ slot : BitVec 64, slot.toNat < capacity.toNat →
      panByteAlignHOL (used + slot) ≠ order + position * 8 ∧
      panByteAlignHOL (used + slot) ≠ orderPos + hole * 8)
    (storeReverse : ∀ slot : BitVec 64, slot.toNat < capacity.toNat → slot ≠ hole →
      orderPos + slot * 8 ≠ order + position * 8 ∧ orderPos + slot * 8 ≠ orderPos + hole * 8)
    (orderEntries : HashOrderEntriesBound order capacity items state)
    (holeInside : hole.toNat < capacity.toNat)
    (copyOrder : ∀ index : BitVec 64, index.toNat < items.toNat → ∀ offset : Nat, offset < size.toNat →
      order + index * 8 ≠ keys + hole * stride + BitVec.ofNat 64 offset ∧
      order + index * 8 ≠ panByteAlignHOL (keys + hole * stride + BitVec.ofNat 64 offset))
    (valueSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ values + hole * 8)
    (orderSeparate : ∀ index : BitVec 64, index.toNat < items.toNat → order + index * 8 ≠ orderPos + hole * 8)
    (positionSeparate : order + position * 8 ≠ orderPos + hole * 8)
    (distinct : ∀ index : BitVec 64, index.toNat < items.toNat → index ≠ position →
      order + index * 8 ≠ order + position * 8) :
    ∃ post, evaluateHOLFiniteState state hashDeleteMoveBody = (none,post) ∧
      state.clock ≤ post.clock + size.toNat + 1 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ HashReverseEntriesBound used orderPos capacity items post ∧ HashOrderEntriesBound order capacity items post ∧
      (∀ slot : BitVec 64, slot.toNat < capacity.toNat →
        hashOccupancyRead post used slot = hashOccupancyRead state used slot) ∧
      post.locals = (setVarHOLFinite (ofString "i") (.val (.word scan)) state).locals := by
  obtain ⟨post,run,cost,remaining,globals,postCode,addresses,endian,reverseValid⟩ :=
    evaluate_hashDelete_move_reverse state keys stride hole scan size values order orderPos position value used capacity items
      keysLocal strideLocal holeLocal scanLocal sizeLocal small aligned scanAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain protectedCells code valuesLocal orderLocal reverseLocal
      valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain
      entries positionBound copyOccupancy copyReverse valueOccupancy valueReverse storeOccupancy storeReverse
  obtain ⟨checked,checkedRun,_,_,_,_,_,_,orderValid⟩ :=
    evaluate_hashDelete_move_order state keys stride hole scan size values order orderPos position value used capacity items
      keysLocal strideLocal holeLocal scanLocal sizeLocal small aligned scanAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain protectedCells code valuesLocal orderLocal reverseLocal
      valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain
      orderEntries holeInside copyOrder valueSeparate orderSeparate positionSeparate distinct
  have same := congrArg Prod.snd (run.symm.trans checkedRun)
  change post = checked at same
  obtain ⟨observed,observedRun,_,_,_,_,_,_,occupancy,locals⟩ :=
    evaluate_hashDelete_move_occupancy state keys stride hole scan size values order orderPos position value capacity used
      keysLocal strideLocal holeLocal scanLocal sizeLocal small aligned scanAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain protectedCells code valuesLocal orderLocal reverseLocal
      valueDomain valueCell destinationDomain loadDomain loadCell separate orderDomain reverseDomain
      copyOccupancy (fun slot inside => ⟨valueOccupancy slot inside,storeOccupancy slot inside⟩)
  have observedSame := congrArg Prod.snd (run.symm.trans observedRun)
  change post = observed at observedSame
  exact ⟨post,run,cost,remaining,globals,postCode,addresses,endian,reverseValid,
    by rw [same]; exact orderValid,
    by rw [observedSame]; exact occupancy,
    by rw [observedSame]; exact locals⟩

#print axioms evaluate_hashDelete_move_invariants
end InitECandidate.Runtime
