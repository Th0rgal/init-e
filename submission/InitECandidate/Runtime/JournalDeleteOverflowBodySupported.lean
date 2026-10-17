import InitECandidate.Runtime.JournalDeleteOverflowBody32
import InitECandidate.Runtime.JournalDeleteAbsent32
import InitECandidate.Runtime.JournalDeleteLookupSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original jdel terminates on journal overflow after its bounded lookup,
without requiring allocator, copy, or growth assumptions. -/
theorem HashTableReady.jdel_overflow_supported {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2.clock + 2 * capacity.toNat + 4 ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2.clock ≤ state.clock := by
  obtain ⟨present,value,looked,_,lookupReady,old,cost,remaining,_,globals,_,_,_,_,run⟩ :=
    ready.jdel_lookup_supported state keyLength table pointer keys stride capacity used values order orderPos items key bits supported arguments keyAligned keyWords keyBytes budget
  have overflow := evaluate_journalDelete_after_get_overflow32 looked present value count journalCapacity lookupReady.live.arrays.code old
    (by rw [globals]; exact countGlobal) (by rw [globals]; exact capacityGlobal) full
  rw [run]
  dsimp only
  refine ⟨overflow.1,?_,?_⟩
  ·
    have bound := overflow.2.1
    have below := overflow.2.2
    omega
  ·
    have bound := overflow.2.1
    have below := overflow.2.2
    omega

#print axioms evaluate_journalDelete_after_get_overflow32
#print axioms HashTableReady.jdel_overflow_supported
end InitECandidate.Runtime
