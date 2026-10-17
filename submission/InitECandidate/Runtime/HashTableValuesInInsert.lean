import InitECandidate.Runtime.HashTableValuesInInsertStores
import InitECandidate.Runtime.HashInsertValueExactMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The executed original post-copy insertion suffix preserves registered
value membership while marking occupancy and updating count/order metadata. -/
theorem HashTableArraysInvariant.insert_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values value order orderPos count index cell : BitVec 64) (bits : Nat)
    (invariant : HashTableArraysInvariant keyLength table keys stride capacity used values order orderPos count bits state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (orderLocal : state.locals.lookup (ofString "order") = some (.val (.word order)))
    (orderPosLocal : state.locals.lookup (ofString "order_pos") = some (.val (.word orderPos)))
    (usedLocal : state.locals.lookup (ofString "used") = some (.val (.word used)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (inside : index.toNat < capacity.toNat)
    (byteMemory : state.memory (panByteAlignHOL (used + index)) = .word cell)
    (empty : hashOccupancyRead state used index = some 0)
    (targets : Set (BitVec 64)) (entries : HashTableValuesIn table targets state) (member : value ∈ targets) :
    ∃ post, evaluateHOLFiniteState state hashInsertValueTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      HashTableValuesIn table targets post ∧ post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧ post.clock = state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  obtain ⟨post,run,memory,header,agreement,clock,globals,code,domain,endian,_⟩ :=
    evaluate_hashInsert_value_tail_exact_memory state capacity used table values value order orderPos count index cell
      tableLocal orderLocal orderPosLocal usedLocal indexLocal valueLocal inside
      facts.valuesDomain facts.valuesMemory (facts.valueDomain index inside) (facts.byteDomain index inside) byteMemory empty
      facts.orderDomain (facts.orderPosDomain index inside) facts.countDomain facts.countMemory facts.agreement facts.noWrap
      (facts.valueCountSeparate index inside) (facts.valueSeparate index inside) (facts.separate index inside)
  have stored := entries.insert_value_stores state keyLength table keys stride capacity used values order orderPos count index cell value bits
    invariant targets member inside byteMemory
  exact ⟨post,run,stored.after_read memory domain endian,header,agreement,clock,globals,code,domain,endian⟩

#print axioms HashTableArraysInvariant.insert_values_in
end InitECandidate.Runtime
