import InitECandidate.Runtime.HashTableArraysFrame32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An old-array word between the header and fresh arrays is outside every
possible new insertion copy/store destination. -/
theorem HashTableArraysInvariant32.earlier_word_separation {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count watched : BitVec 64) (bits frontier : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
    (afterHeader : table.toNat + 72 ≤ watched.toNat) (earlier : watched.toNat < frontier) :
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < 32 →
      watched ≠ keys + slot * stride + BitVec.ofNat 64 offset ∧
      watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) ∧
    (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
      watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) ∧
    watched ≠ order + count * 8 ∧ watched ≠ table + 24 := by
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have orr := invariant.orderBefore
  have limit := invariant.endBound
  have ku := invariant.keysBefore
  have fits := invariant.fits
  have lowerWord : ∀ base : BitVec 64, base.toNat % 8 = 0 →
      base.toNat + capacity.toNat * 8 ≤ 33806089496 →
      ∀ index : BitVec 64, index.toNat < capacity.toNat → base.toNat ≤ (base + index * 8).toNat := by
    intro base aligned bound index inside
    have address := hashFind_slot_address base index 8 capacity inside
      (by change base.toNat + capacity.toNat * 8 ≤ 33806089496; exact bound) aligned (by decide)
    rw [address.1]
    omega
  refine ⟨?_,?_,?_,?_⟩
  · intro slot inside
    have selected := hashFind_slot_address keys slot stride capacity inside (by omega) invariant.keysAligned invariant.strideAligned
    have next := Nat.mul_le_mul_right stride.toNat (show slot.toNat + 1 ≤ capacity.toNat by omega)
    rw [Nat.add_mul,Nat.one_mul] at next
    apply memcpy_interval_separate (keys + slot * stride) 32 watched selected.2
      (by change (keys + slot * stride).toNat + 32 ≤ 33806089496; omega)
    left
    omega
  · intro slot inside
    have vl := lowerWord values invariant.valuesAligned (by omega) slot inside
    have rl := lowerWord orderPos invariant.orderPosAligned limit slot inside
    have ul := hashOccupancy_aligned_interval used capacity slot invariant.usedAligned (by omega) inside
    refine ⟨?_,?_,?_⟩ <;> intro same <;>
      have equal := congrArg BitVec.toNat same <;> omega
  · have ol := lowerWord order invariant.orderAligned (by omega) count invariant.room
    intro same
    have equal := congrArg BitVec.toNat same
    omega
  · have address : (table + (24 : BitVec 64)).toNat = table.toNat + 24 := by
      rw [BitVec.toNat_add_of_lt (by change table.toNat + 24 < 2 ^ 64; have := watched.isLt; omega)]
      rfl
    intro same
    have equal := congrArg BitVec.toNat same
    rw [address] at equal
    omega

theorem HashTableArraysInvariant32.insert_preserves_earlier {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits frontier : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (beforeKeys : frontier ≤ keys.toNat) (beforeValues : frontier ≤ values.toNat)
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
      ∀ watched : BitVec 64, table.toNat + 72 ≤ watched.toNat → watched.toNat < frontier →
        post.memory watched = state.memory watched := by
  obtain ⟨post,run,valid,cost,remaining,locals,globals,addresses,endian,frame⟩ :=
    invariant.insert_with_frame state table keys stride capacity used values order orderPos count key value bits
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  refine ⟨post,run,valid,cost,remaining,locals,globals,addresses,endian,?_⟩
  intro watched afterHeader earlier
  have separate := invariant.earlier_word_separation state table keys stride capacity used values order orderPos count watched bits frontier
    beforeKeys beforeValues afterHeader earlier
  exact frame watched separate.1 separate.2.1 separate.2.2.1 separate.2.2.2

#print axioms HashTableArraysInvariant32.insert_preserves_earlier

#print axioms HashTableArraysInvariant32.earlier_word_separation
end InitECandidate.Runtime
