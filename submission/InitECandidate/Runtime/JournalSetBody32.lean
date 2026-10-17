import InitECandidate.Runtime.JournalSetAfterGet32
import InitECandidate.Runtime.JournalSetLookup32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original jset body for a successful guarded allocation plan. -/
theorem HashTableReady32.jset_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (ticks : 4 * capacity.toNat + 2 * (capacity * 2).toNat + 82 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
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
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer 32) post) ∨
       HashTableReady32 table (allocationEnd pointer 32) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer 32) capacity stride)
        (htabGrowValues (allocationEnd pointer 32) capacity stride) (htabGrowOrder (allocationEnd pointer 32) capacity stride)
        (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) post) ∧
      state.clock ≤ post.clock + 4 * capacity.toNat + 2 * (capacity * 2).toNat + 82 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,keyLocal]
  have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply sourceWordDomain
    simp at member
    omega
  obtain ⟨present,oldValue,looked,_,lookupReady,old,lookupCost,lookupRemaining,memory,globals,code,domain,endian,locals,lookupRun⟩ :=
    ready.jset_lookup state table pointer keys stride capacity used values order orderPos items key bits arguments sourceAligned keyDomain (by omega)
  obtain ⟨post,run,cases,cost,remaining,postCode,postDomain,postEndian⟩ :=
    lookupReady.jset_after_get_safe_plan looked table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue value bits
      ((locals (ofString "key") (by decide)).trans keyLocal) request sourceAligned (by omega)
      (by rw [domain]; exact wordDomain) (by rw [domain]; exact byteDomain)
      (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      ((locals (ofString "t") (by decide)).trans t) old
      (by rw [globals]; exact journalGlobal) (by rw [globals]; exact countGlobal) (by rw [globals]; exact capacityGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
      ((locals (ofString "value") (by decide)).trans v) strideBound safePlan capacityLarge (by rw [domain]; exact growDomain)
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "old",state.locals.lookup (ofString "old"))}
  refine ⟨restored,?_,?_,?_,?_,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [lookupRun,run]
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

#print axioms HashTableReady32.jset_safe_plan
end InitECandidate.Runtime
