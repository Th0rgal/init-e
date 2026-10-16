import InitECandidate.Runtime.HashTableArraysInvariant32
import InitECandidate.Runtime.HashInsertCallEntries32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableArraysInvariant32.insert_order_entries {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat) (budget : capacity.toNat + 35 ≤ state.clock)
    (entries : HashOrderEntriesBound order capacity count state) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableArraysInvariant32 table keys stride capacity used values order orderPos (count + 1) bits post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
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
  obtain ⟨post,run,valid,cost,remaining,locals,globals,addresses,endian⟩ :=
    invariant.insert state table keys stride capacity used values order orderPos count key value bits
      tableArgument keyArgument valueArgument arguments keyAligned sourceWordDomain sourceByteDomain roomAfter budget
  obtain ⟨checked,checkedRun,checkedEntries,_⟩ := evaluate_hashInsert32_call_entries state tableArgument keyArgument valueArgument
    table keys stride key capacity used values value order orderPos count bits invariant.code invariant.power
    (headerDomain 16 (by decide)) invariant.cell16 (headerDomain 0 (by decide)) invariant.cell0
    (headerDomain 8 (by decide)) invariant.cell8 (headerDomain 32 (by decide)) invariant.cell32
    (headerDomain 48 (by decide)) invariant.cell48 (headerDomain 56 (by decide)) invariant.cell56
    (headerDomain 64 (by decide)) invariant.cell64 facts invariant.keysAligned invariant.strideAligned keyAligned
    invariant.usedAligned hk ku (by omega) invariant.fits arrayDomain sourceWordDomain sourceByteDomain readable
    (by rw [← invariant.agreement]; exact invariant.room) budget arguments entries
    invariant.valuesAligned invariant.orderAligned invariant.orderPosAligned (by omega) vu uo orr limit invariant.room
  have equal : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  exact ⟨post,run,valid,by rw [equal]; exact checkedEntries,cost,remaining,locals,globals,addresses,endian⟩

#print axioms HashTableArraysInvariant32.insert_order_entries
end InitECandidate.Runtime
