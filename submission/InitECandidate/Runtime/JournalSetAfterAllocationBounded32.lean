import InitECandidate.Runtime.JournalSetCopyRecord32
import InitECandidate.Runtime.JournalSetFinishBounded32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original post-allocation journal set bound across growth outcomes. -/
theorem HashTableReady32.jset_after_allocation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (small : savedKey.toNat + 32 ≤ 33806089496)
    (aligned : savedKey.toNat % 8 = 0) (sourceAligned : key.toNat % 8 = 0) (ticks : 3 * capacity.toNat + 2 * (capacity * 2).toNat + 78 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (savedKey + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (savedKey + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outside : savedKey.toNat + 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ savedKey.toNat)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (inside : count.toNat < journalCapacity.toNat)
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)
    (v : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (strideBound : stride.toNat ≤ 56)
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address) :
    (evaluateHOLFiniteState state journalSetCopy32).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state journalSetCopy32).2.clock +
        3 * capacity.toNat + 2 * (capacity * 2).toNat + 78 + items.toNat * ((capacity * 2).toNat + 36) ∧
      (evaluateHOLFiniteState state journalSetCopy32).2.clock ≤ state.clock := by
  obtain ⟨recorded,recordReady,copyCost,copyRemaining,globals,code,domain,endian,locals,copyRun⟩ :=
    ready.jset_copy_record state table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue bits
      kc keyLocal klen small aligned sourceAligned (by omega) wordDomain byteDomain sourceWordDomain sourceByteDomain outside
      t old journalGlobal countGlobal inside journalBound journalAligned journalOutside journalDomain
  have bounded := recordReady.jset_finish_bounded recorded table pointer keys stride capacity used values order orderPos items key value count bits
    strideBound (by omega) (by rw [domain]; exact growDomain)
    ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "key") (by decide)).trans keyLocal)
    ((locals (ofString "value") (by decide)).trans v) (by rw [globals]; exact countGlobal)
    capacityLarge sourceAligned (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
  rw [copyRun]
  dsimp only
  exact ⟨bounded.1,by have cost := bounded.2.1; omega,by have remaining := bounded.2.2; omega⟩

#print axioms HashTableReady32.jset_after_allocation_bounded
end InitECandidate.Runtime
