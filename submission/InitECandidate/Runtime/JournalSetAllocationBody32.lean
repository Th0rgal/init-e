import InitECandidate.Runtime.JournalSetAllocate32
import InitECandidate.Runtime.JournalSetAfterAllocation32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original jset allocation and complete following body preserve live tables. -/
theorem HashTableReady32.jset_allocation_body_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (sourceAligned : key.toNat % 8 = 0) (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 79 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
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
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe (allocationEnd pointer 32) (htabGrowAllocationSizes capacity stride))
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos (allocationEnd pointer 32) capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer 32) post) ∨
       HashTableReady32 table (allocationEnd pointer 32) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer 32) capacity stride)
        (htabGrowValues (allocationEnd pointer 32) capacity stride) (htabGrowOrder (allocationEnd pointer 32) capacity stride)
        (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 79 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨allocated,allocatedReady,kc,locals,globals,clock,memory,code,domain,endian,allocateRun⟩ :=
    ready.jset_allocate state table pointer keys stride capacity used values order orderPos items bits klen (by omega) request
  have small : pointer.toNat + 32 ≤ 33806089496 :=
    allocationGuard_sum_bound pointer 32 ready.live.frontier.bounded request
  obtain ⟨post,run,cases,cost,remaining,postCode,postDomain,postEndian⟩ :=
    allocatedReady.jset_after_allocation_safe_plan allocated table (allocationEnd pointer 32) keys stride capacity used values order orderPos items pointer key journal count journalCapacity present oldValue value bits
      kc ((locals (ofString "key") (by decide)).trans keyLocal) ((locals (ofString "klen") (by decide)).trans klen)
      small ready.live.frontier.aligned sourceAligned (by omega)
      (by rw [domain]; exact wordDomain) (by rw [domain]; exact byteDomain)
      (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      (Or.inr ready.live.frontier.allocated) ((locals (ofString "t") (by decide)).trans t)
      ((locals (ofString "old") (by decide)).trans old)
      ((globals (ofString "journal") (by decide)).trans journalGlobal)
      ((globals (ofString "journal_n") (by decide)).trans countGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
      ((locals (ofString "value") (by decide)).trans v) strideBound safePlan capacityLarge (by rw [domain]; exact growDomain)
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "kc",state.locals.lookup (ofString "kc"))}
  refine ⟨restored,?_,?_,?_,?_,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [allocateRun,run]
  · rcases cases with unchanged | grown
    · obtain ⟨nextCount,counts,valid⟩ := unchanged
      exact Or.inl ⟨nextCount,counts,valid.after_read post restored table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer 32) rfl rfl rfl rfl rfl⟩
    · exact Or.inr (grown.after_read post restored table (allocationEnd pointer 32) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer 32) capacity stride)
        (htabGrowValues (allocationEnd pointer 32) capacity stride) (htabGrowOrder (allocationEnd pointer 32) capacity stride) (htabGrowOrderPos (allocationEnd pointer 32) capacity stride)
        (items + 1) (bits + 1) (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl)
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady32.jset_allocation_body_safe_plan
end InitECandidate.Runtime
