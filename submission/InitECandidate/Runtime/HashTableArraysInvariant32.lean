import InitECandidate.Runtime.HashInsertHeaderCall32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Live table facts for arbitrary ordered arrays, allowing growth to relocate
all arrays while keeping the original header. -/
structure HashTableArraysInvariant32 {F : Type}
    (table keys stride capacity used values order orderPos count : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  code : state.code = originalRuntimeCode
  power : capacity.toNat = 2 ^ bits
  keysAligned : keys.toNat % 8 = 0
  strideAligned : stride.toNat % 8 = 0
  valuesAligned : values.toNat % 8 = 0
  usedAligned : used.toNat % 8 = 0
  orderAligned : order.toNat % 8 = 0
  orderPosAligned : orderPos.toNat % 8 = 0
  headerKeys : table.toNat + 72 ≤ keys.toNat
  headerValues : table.toNat + 72 ≤ values.toNat
  keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat
  valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat
  usedBefore : used.toNat + capacity.toNat ≤ order.toNat
  orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat
  endBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496
  fits : 32 ≤ stride.toNat
  domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
    address.toNat < orderPos.toNat + capacity.toNat * 8 → state.memaddrs address
  cell0 : state.memory (table + 0) = .word (32 : BitVec 64)
  cell8 : state.memory (table + 8) = .word stride
  cell16 : state.memory (table + 16) = .word capacity
  cell24 : state.memory (table + 24) = .word count
  cell32 : state.memory (table + 32) = .word keys
  cell40 : state.memory (table + 40) = .word values
  cell48 : state.memory (table + 48) = .word used
  cell56 : state.memory (table + 56) = .word order
  cell64 : state.memory (table + 64) = .word orderPos
  agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used)
  room : count.toNat < capacity.toNat

/-- Insertion preserves an arbitrary allocated table layout, not just the
initial constructor addresses. -/
theorem HashTableArraysInvariant32.insert {F : Type} (state : PanSemStateFiniteExact 64 F)
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
  obtain ⟨post,run,header,agreement,cost,remaining,locals,globals,code,addresses,endian,headers⟩ :=
    evaluate_hashInsert32_call_headers state tableArgument keyArgument valueArgument
      table keys stride key capacity used values value order orderPos count bits invariant.code invariant.power
      (headerDomain 16 (by decide)) invariant.cell16 (headerDomain 0 (by decide)) invariant.cell0
      (headerDomain 8 (by decide)) invariant.cell8 (headerDomain 32 (by decide)) invariant.cell32
      (headerDomain 48 (by decide)) invariant.cell48 (headerDomain 56 (by decide)) invariant.cell56
      (headerDomain 64 (by decide)) invariant.cell64 facts invariant.keysAligned invariant.strideAligned keyAligned
      invariant.usedAligned hk ku (by omega) invariant.fits arrayDomain sourceWordDomain sourceByteDomain readable
      (by rw [← invariant.agreement]; exact invariant.room) invariant.valuesAligned invariant.orderAligned invariant.orderPosAligned
      hv vu uo orr limit budget arguments
  refine ⟨post,run,?_,cost,remaining,locals,globals,addresses,endian⟩
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

#print axioms HashTableArraysInvariant32.insert
end InitECandidate.Runtime
