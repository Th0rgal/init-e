import InitECandidate.Runtime.JournalSetAllocationBody32
import InitECandidate.Runtime.JournalSetGuard32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete successful original jset body after its initial lookup. -/
theorem HashTableReady32.jset_after_get_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (ticks : 2 * capacity.toNat + 2 * (capacity * 2).toNat + 79 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]))
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
    ∃ post, evaluateHOLFiniteState state journalSetAfterGet32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer 32) post) ∨
       HashTableReady32 table (allocationEnd pointer 32) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer 32) capacity stride)
        (htabGrowValues (allocationEnd pointer 32) capacity stride) (htabGrowOrder (allocationEnd pointer 32) capacity stride)
        (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) post) ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 * (capacity * 2).toNat + 79 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "klen") (.val (.word (32 : BitVec 64))) state
  have entryReady := ready.after_read state entered table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have locals : ∀ name, name ≠ ofString "klen" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have klen : entered.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,run,cases,cost,remaining,code,domain,endian⟩ :=
    entryReady.jset_allocation_body_safe_plan entered table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue value bits
      ((locals (ofString "key") (by decide)).trans keyLocal) request klen sourceAligned ticks
      wordDomain byteDomain sourceWordDomain sourceByteDomain
      ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "old") (by decide)).trans old)
      journalGlobal countGlobal inside journalBound journalAligned journalOutside journalDomain
      ((locals (ofString "value") (by decide)).trans v) strideBound safePlan capacityLarge growDomain
  have guard := evaluate_journalSet_guard32 state table count journalCapacity t countGlobal capacityGlobal inside
    (ready.live.arrays.header_domain state table keys stride capacity used values order orderPos items bits 0 (by decide)) ready.live.arrays.cell0
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "klen",state.locals.lookup (ofString "klen"))}
  refine ⟨restored,?_,?_,cost,remaining,code,domain,endian⟩
  · rw [guard]
    change (let output := evaluateHOLFiniteState entered (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalSetCopy32); _) = _
    rw [run]
  · rcases cases with unchanged | grown
    · obtain ⟨nextCount,counts,valid⟩ := unchanged
      exact Or.inl ⟨nextCount,counts,valid.after_read post restored table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer 32) rfl rfl rfl rfl rfl⟩
    · exact Or.inr (grown.after_read post restored table (allocationEnd pointer 32) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer 32) capacity stride)
        (htabGrowValues (allocationEnd pointer 32) capacity stride) (htabGrowOrder (allocationEnd pointer 32) capacity stride) (htabGrowOrderPos (allocationEnd pointer 32) capacity stride)
        (items + 1) (bits + 1) (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl)

#print axioms HashTableReady32.jset_after_get_safe_plan
end InitECandidate.Runtime
