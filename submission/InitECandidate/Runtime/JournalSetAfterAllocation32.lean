import InitECandidate.Runtime.JournalSetCopyRecord32
import InitECandidate.Runtime.JournalSetFinishReady32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original post-allocation jset body, including table growth. -/
theorem HashTableReady32.jset_after_allocation_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (small : savedKey.toNat + 32 ≤ 33806089496)
    (aligned : savedKey.toNat % 8 = 0) (sourceAligned : key.toNat % 8 = 0) (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 78 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
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
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe pointer (htabGrowAllocationSizes capacity stride))
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos pointer capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state journalSetCopy32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos nextCount bits pointer post) ∨
       HashTableReady32 table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride)
        (htabGrowOrderPos pointer capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 78 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨recorded,recordReady,copyCost,copyRemaining,globals,code,domain,endian,locals,copyRun⟩ :=
    ready.jset_copy_record state table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue bits
      kc keyLocal klen small aligned sourceAligned (by omega) wordDomain byteDomain sourceWordDomain sourceByteDomain outside
      t old journalGlobal countGlobal inside journalBound journalAligned journalOutside journalDomain
  obtain ⟨post,run,cases,cost,remaining,postCode,postDomain,postEndian⟩ :=
    recordReady.jset_finish_safe_plan recorded table pointer keys stride capacity used values order orderPos items key value count bits
      strideBound safePlan (by omega) (by rw [domain]; exact growDomain)
      ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "key") (by decide)).trans keyLocal)
      ((locals (ofString "value") (by decide)).trans v) (by rw [globals]; exact countGlobal)
      capacityLarge sourceAligned (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "r",state.locals.lookup (ofString "r"))}
  refine ⟨restored,?_,?_,?_,?_,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [copyRun,run]
  · rcases cases with unchanged | grown
    · obtain ⟨nextCount,counts,valid⟩ := unchanged
      exact Or.inl ⟨nextCount,counts,valid.after_read post restored table keys stride capacity used values order orderPos nextCount bits pointer rfl rfl rfl rfl rfl⟩
    · exact Or.inr (grown.after_read post restored table pointer stride (capacity * 2) (htabGrowUsed pointer capacity stride)
        (htabGrowValues pointer capacity stride) (htabGrowOrder pointer capacity stride) (htabGrowOrderPos pointer capacity stride)
        (items + 1) (bits + 1) (allocationEnd (htabGrowOrderPos pointer capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl)
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady32.jset_after_allocation_safe_plan
end InitECandidate.Runtime
