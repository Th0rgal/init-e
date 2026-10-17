import InitECandidate.Runtime.JournalSetGrowthBoundedOtherSupported
import InitECandidate.Runtime.JournalSetAllocationFailureBodySupported
import InitECandidate.Runtime.JournalSetOverflowBodySupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.jset_supported_bounded_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (sourceAligned : key.toNat % 8 = 0) (ticks : 2 ^ 72 + 2 * capacity.toNat + keyLength.toNat + 5 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (strideBound : stride.toNat ≤ 56)
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2.clock + 2 ^ 72 + 2 * capacity.toNat + keyLength.toNat + 5 ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2.clock ≤ state.clock := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,keyLocal]
  by_cases room : count.toNat < journalCapacity.toNat
  · by_cases request : keyLength ≤ (33806089496 : BitVec 64) - pointer
    · exact ready.jset_growth_supported_bounded_with_other state keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value bits supported
        keyLocal request sourceAligned ticks wordDomain byteDomain sourceWordDomain sourceByteDomain t journalGlobal countGlobal capacityGlobal
        room journalBound journalAligned journalOutside journalDomain v strideBound capacityLarge growDomain
        otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady otherJournalOutside separate beforeKeys beforeValues
    · have failure : ((33806089496 : BitVec 64) - pointer).toNat < keyLength.toNat :=
        Nat.lt_of_not_ge (fun le => request (BitVec.le_def.mpr le))
      have rejected := ready.jset_allocation_failure_supported state keyLength table pointer keys stride capacity used values order orderPos items key count journalCapacity bits supported
        arguments t sourceAligned sourceWordDomain sourceByteDomain (by omega) countGlobal capacityGlobal room failure
      exact ⟨rejected.1,by have cost := rejected.2.1; omega,rejected.2.2⟩
  · have overflow := ready.jset_overflow_supported state keyLength table pointer keys stride capacity used values order orderPos items key count journalCapacity bits supported
      arguments sourceAligned sourceWordDomain sourceByteDomain (by omega) countGlobal capacityGlobal (by omega)
    exact ⟨overflow.1,by have cost := overflow.2.1; omega,overflow.2.2⟩

#print axioms HashTableReady.jset_supported_bounded_with_other
end InitECandidate.Runtime
