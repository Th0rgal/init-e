import InitECandidate.Runtime.JournalOverflow32
import InitECandidate.Runtime.JournalSetLookupSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original jset terminates on journal overflow after its bounded lookup,
without requiring allocator, copy, or growth assumptions. -/
theorem HashTableReady.jset_overflow_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key count journalCapacity : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 3 ≤ state.clock)
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (full : journalCapacity.toNat ≤ count.toNat) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2.clock + 2 * capacity.toNat + 4 ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2.clock ≤ state.clock := by
  obtain ⟨_,_,looked,_,lookupReady,_,cost,remaining,_,globals,_,_,_,_,run⟩ :=
    ready.jset_lookup_supported state keyLength table pointer keys stride capacity used values order orderPos items key bits supported arguments keyAligned keyWords keyBytes budget
  have overflow := evaluate_journal_set_overflow32 looked count journalCapacity lookupReady.live.arrays.code
    (by rw [globals]; exact countGlobal) (by rw [globals]; exact capacityGlobal) full
  rw [run]
  dsimp only
  refine ⟨overflow.1,?_,?_⟩
  ·
    rw [overflow.2]
    omega
  ·
    rw [overflow.2]
    omega

#print axioms HashTableReady.jset_overflow_supported
end InitECandidate.Runtime
