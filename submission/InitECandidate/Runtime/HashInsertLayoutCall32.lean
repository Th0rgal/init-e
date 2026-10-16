import InitECandidate.Runtime.HashInsertCall32
import InitECandidate.Runtime.HashInsertLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original insertion call using allocated-region facts. -/
theorem evaluate_hashInsert32_call_from_layout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (table keys stride key capacity used values value order orderPos count : BitVec 64) (bits : Nat)
    (code : state.code = originalRuntimeCode) (power : capacity.toNat = 2 ^ bits)
    (domain16 : state.memaddrs (table + 16)) (cell16 : state.memory (table + 16) = .word capacity)
    (domain0 : state.memaddrs (table + 0)) (cell0 : state.memory (table + 0) = .word (32 : BitVec 64))
    (domain8 : state.memaddrs (table + 8)) (cell8 : state.memory (table + 8) = .word stride)
    (domain32 : state.memaddrs (table + 32)) (cell32 : state.memory (table + 32) = .word keys)
    (domain48 : state.memaddrs (table + 48)) (cell48 : state.memory (table + 48) = .word used)
    (domain56 : state.memaddrs (table + 56)) (cell56 : state.memory (table + 56) = .word order)
    (domain64 : state.memaddrs (table + 64)) (cell64 : state.memory (table + 64) = .word orderPos)
    (valuesAligned : values.toNat % 8 = 0)
    (orderAligned : order.toNat % 8 = 0) (orderPosAligned : orderPos.toNat % 8 = 0)
    (headerValues : table.toNat + 72 ≤ values.toNat)
    (valuesBefore : values.toNat + capacity.toNat * 8 ≤ used.toNat)
    (usedBefore : used.toNat + capacity.toNat ≤ order.toNat)
    (orderBefore : order.toNat + capacity.toNat * 8 ≤ orderPos.toNat)
    (endBound : orderPos.toNat + capacity.toNat * 8 ≤ 33806089496)
    (tableDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < orderPos.toNat + capacity.toNat * 8 → state.memaddrs address)
    (valuesMemory : state.memory (table + 40) = .word values)
    (countMemory : state.memory (table + 24) = .word count)
    (countAgreement : count.toNat = hashOccupiedCount capacity (hashOccupancyRead state used))
    (keysAligned : keys.toNat % 8 = 0) (strideAligned : stride.toNat % 8 = 0)
    (keyAligned : key.toNat % 8 = 0) (usedAligned : used.toNat % 8 = 0)
    (headerBefore : table.toNat + 72 ≤ keys.toNat)
    (keysBefore : keys.toNat + capacity.toNat * stride.toNat ≤ used.toNat)
    (usedBound : used.toNat + capacity.toNat ≤ 33806089496) (fits : 32 ≤ stride.toNat)
    (arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address)
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (readable : ∀ current : BitVec 64, current.toNat < capacity.toNat → ∃ byte, hashOccupancyRead state used current = some byte)
    (room : hashOccupiedCount capacity (hashOccupancyRead state used) < capacity.toNat)
    (budget : capacity.toNat + 35 ≤ state.clock)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)]) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_insert_raw")
        [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + capacity.toNat + 35 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals := by
  have facts := hashInsert_table_memory_from_layout capacity used table values order orderPos count state
    valuesAligned usedAligned orderAligned orderPosAligned headerValues valuesBefore usedBefore orderBefore endBound
    tableDomain valuesMemory countMemory countAgreement (by rw [countAgreement]; exact room)
  exact evaluate_hashInsert32_call state tableArgument keyArgument valueArgument
    table keys stride key capacity used values value order orderPos count bits code power
    domain16 cell16 domain0 cell0 domain8 cell8 domain32 cell32 domain48 cell48 domain56 cell56 domain64 cell64
    facts keysAligned strideAligned keyAligned usedAligned headerBefore keysBefore usedBound fits
    arrayDomain sourceWordDomain sourceByteDomain readable room budget arguments

#print axioms evaluate_hashInsert32_call_from_layout
end InitECandidate.Runtime
