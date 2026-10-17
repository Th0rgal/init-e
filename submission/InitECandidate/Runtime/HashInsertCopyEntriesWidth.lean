import InitECandidate.Runtime.HashInsertCopyOrderedEntries
import InitECandidate.Runtime.HashInsertCopyBounds
import InitECandidate.Runtime.HashInsertCopyEntries
import InitECandidate.Runtime.HashInsertValueEntriesWidth
import InitECandidate.Runtime.HashInsertCopyOrderedMemory
import InitECandidate.Runtime.HashValueCopyGeometryWidth
import InitECandidate.Runtime.HashReverseCopyGeometryWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original variable-length key-copy and insertion, with all separation premises
obtained from the table allocation layout. -/
theorem HashTableArraysInvariant.insert_copy_entries_width {F : Type} (state : PanSemStateFiniteExact 64 F)
    (capacity used table values value order orderPos count index cell keys stride key keyLength : BitVec 64) (bits : Nat)
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
    (keysLocal : state.locals.lookup (ofString "keys") = some (.val (.word keys)))
    (strideLocal : state.locals.lookup (ofString "stride") = some (.val (.word stride)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (lengthLocal : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (sourceAligned : key.toNat % 8 = 0)
    (budget : keyLength.toNat + 1 ≤ state.clock)
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (keysBeforeValues : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat)
    (entries : HashValueEntriesWord used values capacity state)
    (reverseEntries : HashReverseEntriesBound used orderPos capacity count state)
    (orderEntries : HashOrderEntriesBound order capacity count state) :
    ∃ post, evaluateHOLFiniteState state hashInsertCopyTail = (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      post.memory (table + 24) = .word (count + 1) ∧
      (count + 1).toNat = hashOccupiedCount capacity (hashOccupancyRead post used) ∧
      state.clock ≤ post.clock + keyLength.toNat + 1 ∧ post.clock ≤ state.clock ∧
      HashValueEntriesWord used values capacity post ∧ HashReverseEntriesBound used orderPos capacity (count + 1) post ∧
      HashOrderEntriesBound order capacity (count + 1) post ∧
      post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have facts := invariant.insertion_memory state keyLength table keys stride capacity used values order orderPos count bits
  have ready : HashInsertTailReady capacity used table values value order orderPos count index cell state := {
    tableLocal := tableLocal
    orderLocal := orderLocal
    orderPosLocal := orderPosLocal
    usedLocal := usedLocal
    indexLocal := indexLocal
    valueLocal := valueLocal
    inside := inside
    valuesDomain := facts.valuesDomain
    valuesMemory := facts.valuesMemory
    valueDomain := facts.valueDomain index inside
    byteDomain := facts.byteDomain index inside
    byteMemory := byteMemory
    empty := empty
    orderDomain := facts.orderDomain
    orderPosDomain := facts.orderPosDomain index inside
    countDomain := facts.countDomain
    countMemory := facts.countMemory
    agreement := facts.agreement
    noWrap := facts.noWrap
    valueCountSeparate := facts.valueCountSeparate index inside
    valueSeparate := facts.valueSeparate index inside
    separate := facts.separate index inside
  }
  have hk := invariant.headerKeys
  have ku := invariant.keysBefore
  have uo := invariant.usedBefore
  have oo := invariant.orderBefore
  have bounded := invariant.endBound
  have arrayDomain : ∀ address : BitVec 64, keys.toNat ≤ address.toNat →
      address.toNat < keys.toNat + capacity.toNat * stride.toNat → state.memaddrs address := by
    intro address lower upper
    apply invariant.domain <;> omega
  have bounds := hashInsert_copy_bounds_from_array state table keys stride key keyLength used capacity
    invariant.keysAligned invariant.strideAligned sourceAligned invariant.usedAligned hk ku (by omega)
    invariant.fits arrayDomain sourceWordDomain sourceByteDomain index inside
  have occupancy := memcpy_occupancy_separate (keys + index * stride) keyLength used capacity
    bounds.aligned invariant.usedAligned bounds.copyBefore (by omega)
  have watched := hashInsert_copy_watched_separate table (keys + index * stride) keyLength used capacity index
    ready.inside bounds.aligned invariant.usedAligned bounds.headerBefore bounds.copyBefore (by omega)
  obtain ⟨distinct,byteValues,bookkeeping⟩ := invariant.insert_value_separation_width state keyLength table keys stride capacity used values order orderPos count index bits ready.inside
  obtain ⟨newSeparate,reverseSeparate⟩ := invariant.insert_reverse_separation_width state keyLength table keys stride capacity used values order orderPos count index bits ready.inside
  obtain ⟨post,run,header,agreement,cost,remaining,words,reverse⟩ := evaluate_hashInsert_copy_entries state capacity used table values value order orderPos count index cell keys stride key keyLength
    ready keysLocal strideLocal keyLocal lengthLocal invariant.code bounds.small bounds.aligned sourceAligned budget
    bounds.wordDomain bounds.byteDomain sourceWordDomain sourceByteDomain
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).1)
    (fun offset inside slot slotInside => (occupancy offset inside slot slotInside).2)
    (fun word member offset inside => (watched word member offset inside).1)
    (fun word member offset inside => (watched word member offset inside).2)
    entries distinct byteValues bookkeeping reverseEntries
    (invariant.value_reverse_separate_width state keyLength table keys stride capacity used values order orderPos count index bits ready.inside)
    newSeparate reverseSeparate
    (invariant.delete_copy_values_separate_width state keyLength table keys stride capacity used values order orderPos count index bits ready.inside keysBeforeValues)
    (invariant.delete_copy_reverse_separate_width state keyLength table keys stride capacity used values order orderPos count index bits ready.inside)
  have headerOrder : table.toNat + 72 ≤ order.toNat := by omega
  obtain ⟨checked,checkedRun,ordered,_,_,_,_⟩ := evaluate_hashInsert_copy_ordered_entries state capacity used table values value order orderPos count index cell keys stride key keyLength
    ready keysLocal strideLocal keyLocal lengthLocal invariant.code bounds.small bounds.aligned sourceAligned budget
    bounds.wordDomain bounds.byteDomain sourceWordDomain sourceByteDomain
    invariant.usedAligned bounds.headerBefore bounds.copyBefore bounds.usedBound orderEntries
    invariant.valuesAligned invariant.orderAligned invariant.orderPosAligned headerOrder
    invariant.valuesBefore invariant.usedBefore invariant.orderBefore invariant.endBound invariant.room
  have same := congrArg Prod.snd (run.symm.trans checkedRun)
  change post = checked at same
  obtain ⟨framed,framedRun,_,_,_,_,globals,code,domain,endian,_⟩ := evaluate_hashInsert_copy_tail_ordered_memory state capacity used table values value order orderPos count index cell keys stride key keyLength
    ready keysLocal strideLocal keyLocal lengthLocal invariant.code bounds.small bounds.aligned sourceAligned budget
    bounds.wordDomain bounds.byteDomain sourceWordDomain sourceByteDomain
    invariant.usedAligned bounds.headerBefore bounds.copyBefore bounds.usedBound
  have sameFrame := congrArg Prod.snd (run.symm.trans framedRun)
  change post = framed at sameFrame
  refine ⟨post,run,header,agreement,cost,remaining,words,reverse,?_,?_,?_,?_,?_⟩
  · rw [same]; exact ordered
  · rw [sameFrame]; exact globals
  · rw [sameFrame]; exact code
  · rw [sameFrame]; exact domain
  · rw [sameFrame]; exact endian

#print axioms HashTableArraysInvariant.insert_copy_entries_width
end InitECandidate.Runtime
