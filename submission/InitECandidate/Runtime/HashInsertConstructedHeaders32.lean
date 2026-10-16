import InitECandidate.Runtime.HashInsertHeaderCall32
import InitECandidate.Runtime.HashNewInsertionMemory
import InitECandidate.Runtime.HashNewKeyLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Insertion for the concrete original constructor layout, with header/count
facts and memory domains instead of independent per-slot evaluator premises. -/
theorem evaluate_hashInsert32_constructed_headers {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (table capacity key value count : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (heapBudget : table.toNat + 81 * capacity.toNat + 114 ≤ 33806089496)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabNewOrderPos table 32 capacity).toNat + capacity.toNat * 8 → state.memaddrs address)
    (cell0 : state.memory (table + 0) = .word (32 : BitVec 64))
    (cell8 : state.memory (table + 8) = .word (allocationEnd 0 32))
    (cell16 : state.memory (table + 16) = .word capacity)
    (cell24 : state.memory (table + 24) = .word count)
    (cell32 : state.memory (table + 32) = .word (allocationEnd table 72))
    (cell40 : state.memory (table + 40) = .word (htabNewValues table 32 capacity))
    (cell48 : state.memory (table + 48) = .word (htabNewUsed table 32 capacity))
    (cell56 : state.memory (table + 56) = .word (htabNewOrder table 32 capacity))
    (cell64 : state.memory (table + 64) = .word (htabNewOrderPos table 32 capacity))
    (agreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state (htabNewUsed table 32 capacity)))
    (room : count.toNat < capacity.toNat)
    (keyAligned : key.toNat % 8 = 0)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : capacity.toNat + 35 ≤ state.clock)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post (htabNewUsed table 32 capacity)) ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      ∀ offset : Nat, offset ≤ 64 → offset ≠ 24 →
        post.memory (table + BitVec.ofNat 64 offset) = state.memory (table + BitVec.ofNat 64 offset) := by
  have keyBound : (32 : BitVec 64).toNat ≤ 52 := by decide
  have layout := htabNew_insertion_layout table 32 capacity keyBound heapBudget
  dsimp only at layout
  obtain ⟨ka,sa,fits,hk,ku⟩ := htabNew_key_layout table 32 capacity keyBound heapBudget
  have facts := htabNew_insertion_memory state table 32 capacity count keyBound heapBudget domain cell40 cell24 agreement room
  have headerDomain : ∀ offset : Nat, offset ≤ 64 → state.memaddrs (table + BitVec.ofNat 64 offset) := by
    intro offset small
    have natural : (BitVec.ofNat 64 offset).toNat = offset := by
      change offset % 2 ^ 64 = offset
      exact Nat.mod_eq_of_lt (by omega)
    have address : (table + BitVec.ofNat 64 offset).toNat = table.toNat + offset := by
      rw [BitVec.toNat_add_of_lt (by rw [natural]; omega),natural]
    apply domain
    · omega
    · omega
  have arrayDomain : ∀ address : BitVec 64, (allocationEnd table 72).toNat ≤ address.toNat →
      address.toNat < (allocationEnd table 72).toNat + capacity.toNat * (allocationEnd 0 (32 : BitVec 64)).toNat → state.memaddrs address := by
    intro address lower upper
    exact domain address (by omega) (by omega)
  have readable : ∀ current : BitVec 64, current.toNat < capacity.toNat →
      ∃ byte, hashOccupancyRead state (htabNewUsed table 32 capacity) current = some byte := by
    intro current inside
    have available := facts.byteDomain current inside
    unfold hashOccupancyRead panMemLoadByteHOL
    dsimp only
    rw [if_pos available]
    exact ⟨_,rfl⟩
  obtain ⟨va,ua,oa,ra,hv,vu,uo,orr,limit⟩ := layout
  exact evaluate_hashInsert32_call_headers state tableArgument keyArgument valueArgument
    table (allocationEnd table 72) (allocationEnd 0 32) key capacity (htabNewUsed table 32 capacity)
    (htabNewValues table 32 capacity) value (htabNewOrder table 32 capacity) (htabNewOrderPos table 32 capacity) count bits
    code power (headerDomain 16 (by decide)) cell16 (headerDomain 0 (by decide)) cell0
    (headerDomain 8 (by decide)) cell8 (headerDomain 32 (by decide)) cell32
    (headerDomain 48 (by decide)) cell48 (headerDomain 56 (by decide)) cell56 (headerDomain 64 (by decide)) cell64
    facts ka sa keyAligned ua hk ku (by omega) fits arrayDomain sourceWordDomain sourceByteDomain readable
    (by rw [← agreement]; exact room) va oa ra hv vu uo orr limit budget arguments

#print axioms evaluate_hashInsert32_constructed_headers
end InitECandidate.Runtime
