import InitECandidate.Runtime.HashTableArraysFrame32
import InitECandidate.Runtime.MemcpyIntervalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every possible insertion store lies within the table allocation interval. -/
theorem HashTableArraysInvariant32.outside_allocation_separation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count watched : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (outside : watched.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ watched.toNat) :
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      watched ≠ keys + slot * stride + BitVec.ofNat 64 offset ∧ watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
      watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) ∧
    watched ≠ order + count * 8 ∧ watched ≠ table + 24 := by
  have hk := invariant.headerKeys
  have hv := invariant.headerValues
  have ku := invariant.keysBefore
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have fits := invariant.fits
  have different : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < orderPos.toNat + capacity.toNat * 8 → watched ≠ address := by
    intro address lower upper same
    have equal := congrArg BitVec.toNat same
    rcases outside with before | after <;> omega
  have word : ∀ base : BitVec 64, table.toNat ≤ base.toNat →
      base.toNat + capacity.toNat * 8 ≤ orderPos.toNat + capacity.toNat * 8 → base.toNat % 8 = 0 →
      ∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ base + slot * 8 := by
    intro base lower upper aligned slot inside
    have address := (hashFind_slot_address base slot 8 capacity inside (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; omega) aligned (by decide)).1
    change (base + slot * 8).toNat = base.toNat + slot.toNat * 8 at address
    have product := Nat.mul_lt_mul_of_pos_right inside (by decide : 0 < 8)
    apply different <;> omega
  refine ⟨?_,?_,?_,?_⟩
  · intro slot inside
    have selected := hashFind_slot_address keys slot stride capacity inside (by omega) invariant.keysAligned invariant.strideAligned
    have next := Nat.mul_le_mul_right stride.toNat (show slot.toNat + 1 ≤ capacity.toNat by omega)
    rw [Nat.add_mul,Nat.one_mul] at next
    apply memcpy_interval_separate (keys + slot * stride) 32 watched selected.2 (by change (keys + slot * stride).toNat + 32 ≤ 33806089496; omega)
    rcases outside with before | after
    · exact Or.inl (by omega)
    · exact Or.inr (by change (keys + slot * stride).toNat + 32 ≤ watched.toNat; omega)
  · intro slot inside
    refine ⟨word values (by omega) (by omega) invariant.valuesAligned slot inside,?_,word orderPos (by omega) (by omega) invariant.orderPosAligned slot inside⟩
    have interval := hashOccupancy_aligned_interval used capacity slot invariant.usedAligned (by omega) inside
    apply different <;> omega
  · exact word order (by omega) (by omega) invariant.orderAligned count invariant.room
  · have address : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
      rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; omega)]
      rfl
    apply different <;> omega

theorem HashTableArraysInvariant32.insert_preserves_outside_allocation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64, (watched.toNat < table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ watched.toNat) →
        post.memory watched = state.memory watched := by
  obtain ⟨post,run,valid,cost,remaining,locals,globals,addresses,endian,frame⟩ :=
    invariant.insert_with_frame state table keys stride capacity used values order orderPos count key value bits
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  refine ⟨post,run,valid,cost,remaining,locals,globals,addresses,endian,?_⟩
  intro watched outside
  have separate := invariant.outside_allocation_separation state table keys stride capacity used values order orderPos count watched bits outside
  exact frame watched separate.1 separate.2.1 separate.2.2.1 separate.2.2.2

#print axioms HashTableArraysInvariant32.outside_allocation_separation
#print axioms HashTableArraysInvariant32.insert_preserves_outside_allocation
end InitECandidate.Runtime
