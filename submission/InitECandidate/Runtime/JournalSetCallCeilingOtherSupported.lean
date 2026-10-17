import InitECandidate.Runtime.JournalSetCallBoundedOtherSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.jset_call_supported_ceiling_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (sourceAligned : key.toNat % 8 = 0) (ticks : 2 ^ 73 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)
    (strideBound : stride.toNat ≤ 56)
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)]) :
    state.clock ≤ (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2.clock +
      2 ^ 73 ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2.clock ≤ state.clock := by
  have capacityBound : capacity.toNat ≤ 33806089496 := by
    have u := ready.live.arrays.usedBefore
    have o := ready.live.arrays.orderBefore
    have e := ready.live.arrays.endBound
    omega
  have width : keyLength.toNat ≤ 52 := by
    rcases supported with rfl | rfl | rfl <;> decide
  have bounded := ready.jset_call_supported_bounded_with_other state keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value bits supported
    sourceAligned (by omega) wordDomain byteDomain sourceWordDomain sourceByteDomain journalGlobal countGlobal capacityGlobal
    journalBound journalAligned journalOutside journalDomain strideBound capacityLarge growDomain
    otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady otherJournalOutside separate beforeKeys beforeValues
    tableArgument keyArgument valueArgument arguments
  exact ⟨by have cost := bounded.1; omega,bounded.2⟩

#print axioms HashTableReady.jset_call_supported_ceiling_with_other
end InitECandidate.Runtime
