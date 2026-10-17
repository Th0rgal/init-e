import InitECandidate.Runtime.JournalSetGrowthBounded32
import InitECandidate.Runtime.JournalSetAllocationFailureBody32
import InitECandidate.Runtime.JournalSetOverflowBody32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Uniform original jset bound across all journal and allocation outcomes. -/
theorem HashTableReady32.jset_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (sourceAligned : key.toNat % 8 = 0) (ticks : 5 * capacity.toNat + 2 * (capacity * 2).toNat + 82 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
      address.toNat < (htabGrowOrderPos (allocationEnd pointer 32) capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2.clock +
        5 * capacity.toNat + 2 * (capacity * 2).toNat + 82 + items.toNat * ((capacity * 2).toNat + 36) ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2.clock ≤ state.clock := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,keyLocal]
  have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply sourceWordDomain
    simp at member
    omega
  by_cases room : count.toNat < journalCapacity.toNat
  · by_cases request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer
    · exact ready.jset_growth_bounded state table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value bits
        keyLocal request sourceAligned ticks wordDomain byteDomain sourceWordDomain sourceByteDomain t
        journalGlobal countGlobal capacityGlobal room journalBound journalAligned journalOutside journalDomain
        v strideBound capacityLarge growDomain
    · have failure : ((33806089496 : BitVec 64) - pointer).toNat < 32 := by
        have notLe : ¬(32 : BitVec 64).toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat := fun le => request (BitVec.le_def.mpr le)
        change ¬32 ≤ _ at notLe
        omega
      have rejected := ready.jset_allocation_failure state table pointer keys stride capacity used values order orderPos items key count journalCapacity bits
        arguments t sourceAligned keyDomain (by omega) countGlobal capacityGlobal room failure
      exact ⟨rejected.1,by have cost := rejected.2.1; omega,rejected.2.2⟩
  · have overflow := ready.jset_overflow state table pointer keys stride capacity used values order orderPos items key count journalCapacity bits
      arguments sourceAligned keyDomain (by omega) countGlobal capacityGlobal (by omega)
    exact ⟨overflow.1,by have cost := overflow.2.1; omega,overflow.2.2⟩

#print axioms HashTableReady32.jset_bounded
end InitECandidate.Runtime
