import InitECandidate.Runtime.HashOrderLinked
import InitECandidate.Runtime.ListImageCoversRange
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Occupancy/count agreement and the reverse-to-forward link make the order
array complete: every live position names an occupied in-range slot. No extra
forward-occupancy invariant is assumed. -/
theorem HashOrderLinked.order_occupied {F : Type} (state : PanSemStateFiniteExact 64 F)
    (used order orderPos capacity items : BitVec 64)
    (linked : HashOrderLinked used order orderPos capacity items state)
    (agreement : items.toNat = hashOccupiedCount capacity (hashOccupancyRead state used)) :
    ∀ position : BitVec 64, position.toNat < items.toNat → ∃ slot : BitVec 64,
      slot.toNat < capacity.toNat ∧ hashOccupancyRead state used slot ≠ some 0 ∧
      state.memory (order + position * 8) = .word slot := by
  classical
  let occupied := (List.range capacity.toNat).filter (fun index => hashOccupancyRead state used (BitVec.ofNat 64 index) != some 0)
  let reverseIndex := fun index : Nat => (state.memory (orderPos + BitVec.ofNat 64 index * 8)).1.toNat
  have memberFacts (index : Nat) (member : index ∈ occupied) :
      index < capacity.toNat ∧ hashOccupancyRead state used (BitVec.ofNat 64 index) ≠ some 0 := by
    simpa only [occupied,List.mem_filter,List.mem_range,bne_iff_ne] using member
  have wordNat (index : Nat) (member : index ∈ occupied) : (BitVec.ofNat 64 index).toNat = index :=
    Nat.mod_eq_of_lt (Nat.lt_trans (memberFacts index member).1 capacity.isLt)
  have witness (index : Nat) (member : index ∈ occupied) : ∃ position : BitVec 64,
      reverseIndex index = position.toNat ∧ position.toNat < items.toNat ∧
      state.memory (order + position * 8) = .word (BitVec.ofNat 64 index) := by
    have facts := memberFacts index member
    obtain ⟨position,inside,reverse,forward⟩ := linked (BitVec.ofNat 64 index) (by rw [wordNat index member]; exact facts.1) facts.2
    refine ⟨position,?_,inside,forward⟩
    change (state.memory (orderPos + BitVec.ofNat 64 index * 8)).1.toNat = position.toNat
    rw [reverse]
  have distinct : occupied.Nodup := List.filter_sublist.nodup List.nodup_range
  have mappedDistinct : (occupied.map reverseIndex).Nodup := by
    apply list_nodup_map_of_injective_on occupied reverseIndex distinct
    intro first firstMember second secondMember equal
    obtain ⟨left,leftIndex,_,leftForward⟩ := witness first firstMember
    obtain ⟨right,rightIndex,_,rightForward⟩ := witness second secondMember
    have same : left = right := BitVec.eq_of_toNat_eq (leftIndex.symm.trans (equal.trans rightIndex))
    rw [same] at leftForward
    have words : (BitVec.ofNat 64 first) = BitVec.ofNat 64 second := by
      simpa only [HolWordLab.word.injEq] using leftForward.symm.trans rightForward
    have naturals := congrArg BitVec.toNat words
    rw [wordNat first firstMember,wordNat second secondMember] at naturals
    exact naturals
  have mappedBound : ∀ index ∈ occupied, reverseIndex index < items.toNat := by
    intro index member
    obtain ⟨position,equal,inside,_⟩ := witness index member
    rw [equal]; exact inside
  have length : occupied.length = items.toNat := by
    simpa only [hashOccupiedCount,List.countP_eq_length_filter] using agreement.symm
  have covers := list_image_covers_range occupied reverseIndex items.toNat mappedDistinct mappedBound length
  intro position inside
  obtain ⟨index,member,indexEq⟩ := covers position.toNat inside
  obtain ⟨actual,actualIndex,_,forward⟩ := witness index member
  have same : actual = position := BitVec.eq_of_toNat_eq (actualIndex.symm.trans indexEq)
  rw [same] at forward
  exact ⟨BitVec.ofNat 64 index,by rw [wordNat index member]; exact (memberFacts index member).1,
    (memberFacts index member).2,forward⟩

#print axioms HashOrderLinked.order_occupied
end InitECandidate.Runtime
