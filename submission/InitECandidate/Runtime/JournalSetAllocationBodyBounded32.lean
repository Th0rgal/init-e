import InitECandidate.Runtime.JournalSetAllocate32
import InitECandidate.Runtime.JournalSetAfterAllocationBounded32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Journal allocation through return without assuming successful table growth. -/
theorem HashTableReady32.jset_allocation_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (sourceAligned : key.toNat % 8 = 0) (ticks : 3 * capacity.toNat + 2 * (capacity * 2).toNat + 79 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
      address.toNat < (htabGrowOrderPos (allocationEnd pointer 32) capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address) :
    (evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32)).1 ≠ none ∧
      state.clock ≤ (evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32)).2.clock +
        3 * capacity.toNat + 2 * (capacity * 2).toNat + 79 + items.toNat * ((capacity * 2).toNat + 36) ∧
      (evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32)).2.clock ≤ state.clock := by
  obtain ⟨allocated,allocatedReady,kc,locals,globals,clock,memory,code,domain,endian,allocateRun⟩ :=
    ready.jset_allocate state table pointer keys stride capacity used values order orderPos items bits klen (by omega) request
  have small : pointer.toNat + 32 ≤ 33806089496 :=
    allocationGuard_sum_bound pointer 32 ready.live.frontier.bounded request
  have bounded :=
    allocatedReady.jset_after_allocation_bounded allocated table (allocationEnd pointer 32) keys stride capacity used values order orderPos items pointer key journal count journalCapacity present oldValue value bits
      kc ((locals (ofString "key") (by decide)).trans keyLocal) ((locals (ofString "klen") (by decide)).trans klen)
      small ready.live.frontier.aligned sourceAligned (by omega)
      (by rw [domain]; exact wordDomain) (by rw [domain]; exact byteDomain)
      (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      (Or.inr ready.live.frontier.allocated) ((locals (ofString "t") (by decide)).trans t)
      ((locals (ofString "old") (by decide)).trans old)
      ((globals (ofString "journal") (by decide)).trans journalGlobal)
      ((globals (ofString "journal_n") (by decide)).trans countGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
      ((locals (ofString "value") (by decide)).trans v) strideBound capacityLarge (by rw [domain]; exact growDomain)
  rw [allocateRun]
  dsimp only
  exact ⟨bounded.1,by have cost := bounded.2.1; omega,by have remaining := bounded.2.2; omega⟩

#print axioms HashTableReady32.jset_allocation_body_bounded
end InitECandidate.Runtime
