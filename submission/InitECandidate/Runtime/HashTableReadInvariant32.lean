import InitECandidate.Runtime.HashTableInvariant32
import InitECandidate.Runtime.HashFindCall32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Read-only source operations retain all table facts, independent of locals. -/
theorem HashTableInvariant32.after_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table capacity count : BitVec 64) (bits : Nat)
    (invariant : HashTableInvariant32 table capacity count bits state)
    (memory : post.memory = state.memory) (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableInvariant32 table capacity count bits post := by
  have reads : hashOccupancyRead post (htabNewUsed table 32 capacity) =
      hashOccupancyRead state (htabNewUsed table 32 capacity) := by
    funext index
    unfold hashOccupancyRead
    rw [memory,addresses,endian]
  exact {
    code := code.trans invariant.code
    power := invariant.power
    heapBudget := invariant.heapBudget
    domain := by rw [addresses]; exact invariant.domain
    cell0 := by rw [memory]; exact invariant.cell0
    cell8 := by rw [memory]; exact invariant.cell8
    cell16 := by rw [memory]; exact invariant.cell16
    cell24 := by rw [memory]; exact invariant.cell24
    cell32 := by rw [memory]; exact invariant.cell32
    cell40 := by rw [memory]; exact invariant.cell40
    cell48 := by rw [memory]; exact invariant.cell48
    cell56 := by rw [memory]; exact invariant.cell56
    cell64 := by rw [memory]; exact invariant.cell64
    agreement := by rw [reads]; exact invariant.agreement
    room := invariant.room
  }

/-- Every original header load is within the allocated table domain. -/
theorem HashTableInvariant32.header_domain {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count : BitVec 64) (bits : Nat)
    (invariant : HashTableInvariant32 table capacity count bits state)
    (offset : Nat) (small : offset ≤ 64) : state.memaddrs (table + BitVec.ofNat 64 offset) := by
  have layout := htabNew_insertion_layout table 32 capacity (by decide) invariant.heapBudget
  dsimp only at layout
  have limit := invariant.heapBudget
  have natural : (BitVec.ofNat 64 offset).toNat = offset := by
    change offset % 2 ^ 64 = offset
    exact Nat.mod_eq_of_lt (by omega)
  have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
    rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
  apply invariant.domain <;> omega

/-- Actual original find-slot call from the reusable table invariant. -/
theorem HashTableInvariant32.find {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table capacity count key : BitVec 64) (bits : Nat)
    (invariant : HashTableInvariant32 table capacity count bits state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] =
        some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ found : BitVec 64, ∃ ready, found.toNat ≤ capacity.toNat ∧
      state.clock ≤ ready.clock + 2 * capacity.toNat + 2 ∧ ready.clock ≤ state.clock ∧
      ready.memory = state.memory ∧ ready.globals = state.globals ∧ ready.code = state.code ∧
      ready.memaddrs = state.memaddrs ∧ ready.be = state.be ∧ ready.locals = state.locals ∧
      HashTableInvariant32 table capacity count bits ready ∧
      ∀ name continuation, evaluateHOLFiniteState state
        (.decCall name .one (ofString "htab_find_slot") [tableArgument,keyArgument] continuation) =
        (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation;
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name))})) := by
  have layout := htabNew_insertion_layout table 32 capacity (by decide) invariant.heapBudget
  dsimp only at layout
  obtain ⟨ka,sa,fits,hk,ku⟩ := htabNew_key_layout table 32 capacity (by decide) invariant.heapBudget
  have facts := htabNew_insertion_memory state table 32 capacity count (by decide) invariant.heapBudget invariant.domain
    invariant.cell40 invariant.cell24 invariant.agreement invariant.room
  have headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by have := invariant.heapBudget; omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; have := invariant.heapBudget; omega),natural]
    apply invariant.domain <;> omega
  have arrayDomain : ∀ address : BitVec 64, (allocationEnd table 72).toNat ≤ address.toNat →
      address.toNat < (allocationEnd table 72).toNat + capacity.toNat * (allocationEnd 0 (32 : BitVec 64)).toNat → state.memaddrs address := by
    intro address lower upper
    exact invariant.domain address (by omega) (by omega)
  have readable : ∀ current : BitVec 64, current.toNat < capacity.toNat →
      ∃ byte, hashOccupancyRead state (htabNewUsed table 32 capacity) current = some byte := by
    intro current inside
    have available := facts.byteDomain current inside
    unfold hashOccupancyRead panMemLoadByteHOL
    dsimp only
    rw [if_pos available]
    exact ⟨_,rfl⟩
  obtain ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,decl⟩ :=
    evaluate_hashFind32_declaration state tableArgument keyArgument table (allocationEnd table 72) (allocationEnd 0 32) key capacity
      (htabNewUsed table 32 capacity) bits invariant.code invariant.power ka sa keyAligned fits (by omega)
      (headerDomain 16 (by decide)) invariant.cell16 (headerDomain 0 (by decide)) invariant.cell0
      (headerDomain 8 (by decide)) invariant.cell8 (headerDomain 32 (by decide)) invariant.cell32
      (headerDomain 48 (by decide)) invariant.cell48 arrayDomain keyDomain readable
      (by rw [← invariant.agreement]; exact invariant.room) arguments budget
  exact ⟨found,ready,inside,cost,remaining,memory,globals,code,addresses,endian,locals,
    invariant.after_read state ready table capacity count bits memory code addresses endian,decl⟩

#print axioms HashTableInvariant32.header_domain
#print axioms HashTableInvariant32.after_read
#print axioms HashTableInvariant32.find
end InitECandidate.Runtime
