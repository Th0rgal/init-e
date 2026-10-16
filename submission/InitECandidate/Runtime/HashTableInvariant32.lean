import InitECandidate.Runtime.HashInsertConstructedHeaders32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Source table layout, live header values, count agreement and available
capacity, independent of any operation's temporary local environment. -/
structure HashTableInvariant32 {F : Type} (table capacity count : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F) : Prop where
  code : state.code = originalRuntimeCode
  power : capacity.toNat = 2 ^ bits
  heapBudget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496
  domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
    address.toNat < (htabNewOrderPos table 32 capacity).toNat + capacity.toNat * 8 → state.memaddrs address
  cell0 : state.memory (table + 0) = .word (32 : BitVec 64)
  cell8 : state.memory (table + 8) = .word (allocationEnd 0 32)
  cell16 : state.memory (table + 16) = .word capacity
  cell24 : state.memory (table + 24) = .word count
  cell32 : state.memory (table + 32) = .word (allocationEnd table 72)
  cell40 : state.memory (table + 40) = .word (htabNewValues table 32 capacity)
  cell48 : state.memory (table + 48) = .word (htabNewUsed table 32 capacity)
  cell56 : state.memory (table + 56) = .word (htabNewOrder table 32 capacity)
  cell64 : state.memory (table + 64) = .word (htabNewOrderPos table 32 capacity)
  agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state (htabNewUsed table 32 capacity))
  room : count.toNat < capacity.toNat

/-- Actual insertion preserves the table invariant while room remains for a
subsequent operation. No evaluator behavior is assumed by the invariant. -/
theorem HashTableInvariant32.insert {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count key value : BitVec 64) (bits : Nat)
    (invariant : HashTableInvariant32 table capacity count bits state)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (roomAfter : count.toNat + 1 < capacity.toNat)
    (budget : capacity.toNat + 35 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      HashTableInvariant32 table capacity (count + 1) bits post ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,header,agreement,cost,remaining,locals,globals,code,addresses,endian,headers⟩ :=
    evaluate_hashInsert32_constructed_headers state tableArgument keyArgument valueArgument table capacity key value count bits
      invariant.code invariant.power invariant.heapBudget invariant.domain
      invariant.cell0 invariant.cell8 invariant.cell16 invariant.cell24 invariant.cell32 invariant.cell40
      invariant.cell48 invariant.cell56 invariant.cell64 invariant.agreement invariant.room keyAligned
      sourceWordDomain sourceByteDomain budget arguments
  refine ⟨post,run,?_,cost,remaining,locals,globals,addresses,endian⟩
  refine {
    code := code.trans invariant.code
    power := invariant.power
    heapBudget := invariant.heapBudget
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
  have limit := invariant.heapBudget
  have noWrap : count.toNat + (1 : BitVec 64).toNat < 2 ^ 64 := by
    change count.toNat + 1 < 2 ^ 64
    omega
  rw [BitVec.toNat_add_of_lt noWrap]
  exact roomAfter

#print axioms HashTableInvariant32.insert
end InitECandidate.Runtime
