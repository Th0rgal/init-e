import InitECandidate.Runtime.HashTableArraysFrameSupported
import InitECandidate.Runtime.PtKeyULeafKUGD
import InitECandidate.Runtime.HashInsertProbeTailKU
import InitECandidate.Runtime.HashInsertCopyMemoryKU
import InitECandidate.Runtime.HashInsertCopyOrderedMemoryKU
import InitECandidate.Runtime.HashInsertProbeMemoryKU
import InitECandidate.Runtime.HashInsertCopyBoundsKU
import InitECandidate.Runtime.HashInsertProbeArraysMemoryKU
import InitECandidate.Runtime.HashInsertIndexMemoryKU
import InitECandidate.Runtime.HashInsertHashMemorySupportedKU
import InitECandidate.Runtime.HashInsertBodyMemorySupportedKU
import InitECandidate.Runtime.HashInsertCallMemorySupportedKU
/-! Unaligned-key copy of `HashTableArraysFrameSupported` (generated; see PtKeyULeafKUGD): key alignment replaced by `key % 8 ≠ 0`, `8 ≤ keyLength`
and the key fit; lookup budgets made linear in the width bound (`54·cap`). -/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The same actual insertion execution preserves its relocated invariant
and every word separated from all possible copy and store destinations. -/
theorem HashTableArraysInvariant.insert_supported_with_frameKU {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 ≠ 0) (len8 : 8 ≤ keyLength.toNat) (keyFit : key.toNat + keyLength.toNat ≤ 33806089496)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + keyLength.toNat + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos (count + 1) bits post ∧
      state.clock ≤ post.clock + capacity.toNat + keyLength.toNat + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ watched : BitVec 64,
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → ∀ offset : Nat, offset < keyLength.toNat →
          watched ≠ keys + slot * stride + BitVec.ofNat 64 offset ∧
          watched ≠ panByteAlignHOL (keys + slot * stride + BitVec.ofNat 64 offset)) →
        (∀ slot : BitVec 64, slot.toNat < capacity.toNat → watched ≠ values + slot * 8 ∧
          watched ≠ panByteAlignHOL (used + slot) ∧ watched ≠ orderPos + slot * 8) →
        watched ≠ order + count * 8 → watched ≠ table + 24 → post.memory watched = state.memory watched := by
  have limit := invariant.endBound
  have hv := invariant.headerValues
  have vu := invariant.valuesBefore
  have uo := invariant.usedBefore
  have orr := invariant.orderBefore
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply invariant.domain <;> omega
  have facts := hashInsert_table_memory_from_layout capacity used table values order orderPos count state
    invariant.valuesAligned invariant.usedAligned invariant.orderAligned invariant.orderPosAligned hv vu uo orr limit
    invariant.domain invariant.cell40 invariant.cell24 invariant.agreement invariant.room
  have arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address := by
    intro address lower upper
    apply invariant.domain <;> omega
  have readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte := by
    intro current inside
    have available := facts.byteDomain current inside
    unfold hashOccupancyRead panMemLoadByteHOL
    dsimp only
    rw [if_pos available]
    exact ⟨_,rfl⟩
  obtain ⟨post,run,header,agreement,cost,remaining,locals,globals,code,addresses,endian,frame⟩ :=
    evaluate_hashInsert_supported_call_memoryKU state tableArgument keyArgument valueArgument
      table keys stride key capacity used values value order orderPos count keyLength bits supported invariant.code invariant.power
      (headerDomain 16 (by decide)) invariant.cell16 (headerDomain 0 (by decide)) invariant.cell0
      (headerDomain 8 (by decide)) invariant.cell8 (headerDomain 32 (by decide)) invariant.cell32
      (headerDomain 48 (by decide)) invariant.cell48 (headerDomain 56 (by decide)) invariant.cell56
      (headerDomain 64 (by decide)) invariant.cell64 facts invariant.keysAligned invariant.strideAligned keyAligned len8 keyFit
      invariant.usedAligned hk ku (by omega) invariant.fits arrayDomain sourceWordDomain sourceByteDomain readable
      (by rw [← invariant.agreement]; exact invariant.room) budget arguments
  have headers : ∀ offset : Nat, offset ≤ 64 → offset ≠ 24 →
      post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
    intro offset field notCount
    have separate := hashInsert_header_separation_width table keys stride capacity used values order orderPos count keyLength
      invariant.keysAligned invariant.strideAligned invariant.valuesAligned invariant.usedAligned invariant.orderAligned invariant.orderPosAligned
      hk hv ku vu uo orr limit invariant.fits invariant.room offset field notCount
    exact frame _ separate.1 separate.2.1 separate.2.2.1 separate.2.2.2
  refine ⟨post,run,?_,cost,remaining,locals,globals,addresses,endian,frame⟩
  refine {
    code := code.trans invariant.code
    power := invariant.power
    keysAligned := invariant.keysAligned
    strideAligned := invariant.strideAligned
    valuesAligned := invariant.valuesAligned
    usedAligned := invariant.usedAligned
    orderAligned := invariant.orderAligned
    orderPosAligned := invariant.orderPosAligned
    headerKeys := invariant.headerKeys
    headerValues := invariant.headerValues
    keysBefore := invariant.keysBefore
    valuesBefore := invariant.valuesBefore
    usedBefore := invariant.usedBefore
    orderBefore := invariant.orderBefore
    endBound := invariant.endBound
    fits := invariant.fits
    domain := by rw [addresses]; exact invariant.domain
    cell24 := header
    agreement := agreement
    room := ?_
    cell0 := (headers 0 (by decide) (by decide)).trans invariant.cell0
    cell8 := (headers 8 (by decide) (by decide)).trans invariant.cell8
    cell16 := (headers 16 (by decide) (by decide)).trans invariant.cell16
    cell32 := (headers 32 (by decide) (by decide)).trans invariant.cell32
    cell40 := (headers 40 (by decide) (by decide)).trans invariant.cell40
    cell48 := (headers 48 (by decide) (by decide)).trans invariant.cell48
    cell56 := (headers 56 (by decide) (by decide)).trans invariant.cell56
    cell64 := (headers 64 (by decide) (by decide)).trans invariant.cell64
  }
  rw [BitVec.toNat_add_of_lt (by change count.toNat + 1 < 2 ^ 64; omega)]
  exact roomAfter

#print axioms HashTableArraysInvariant.insert_supported_with_frameKU
end InitECandidate.Runtime
