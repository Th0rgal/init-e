import InitECandidate.Runtime.JournalSetAfterGetOtherSupported
import InitECandidate.Runtime.JournalSetLookupSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original jset body for a successful guarded allocation plan. -/
theorem HashTableReady.jset_supported_with_other_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : keyLength ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (ticks : 5 * capacity.toNat + 2 * (capacity * 2).toNat + 2 * keyLength.toNat + 18 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe (allocationEnd pointer keyLength) (htabGrowAllocationSizes capacity stride))
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos (allocationEnd pointer keyLength) capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer keyLength) post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) post) ∨ (HashTableReady keyLength table (allocationEnd pointer keyLength) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer keyLength) capacity stride)
        (htabGrowValues (allocationEnd pointer keyLength) capacity stride) (htabGrowOrder (allocationEnd pointer keyLength) capacity stride) (htabGrowOrderPos (allocationEnd pointer keyLength) capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer keyLength) capacity stride) ((capacity * 2) * 8)) post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer keyLength) capacity stride) ((capacity * 2) * 8)) post)) ∧
      state.clock ≤ post.clock + 5 * capacity.toNat + 2 * (capacity * 2).toNat + 2 * keyLength.toNat + 18 + items.toNat * ((capacity * 2).toNat + keyLength.toNat + 4) ∧
      post.clock ≤ state.clock ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,keyLocal]
  obtain ⟨present,oldValue,looked,_,lookupReady,old,lookupCost,lookupRemaining,memory,globals,code,domain,endian,locals,lookupRun⟩ :=
    ready.jset_lookup_supported state keyLength table pointer keys stride capacity used values order orderPos items key bits supported arguments sourceAligned sourceWordDomain sourceByteDomain (by omega)
  have lookupOther := otherReady.after_read state looked otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer memory globals code domain endian
  obtain ⟨post,run,cases,cost,remaining,postCode,postDomain,postEndian⟩ :=
    lookupReady.jset_after_get_supported_with_other_safe_plan looked keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue value bits supported
      ((locals (ofString "key") (by decide)).trans keyLocal) request sourceAligned (by omega)
      (by rw [domain]; exact wordDomain) (by rw [domain]; exact byteDomain)
      (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      ((locals (ofString "t") (by decide)).trans t) old
      (by rw [globals]; exact journalGlobal) (by rw [globals]; exact countGlobal) (by rw [globals]; exact capacityGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
      ((locals (ofString "value") (by decide)).trans v) strideBound safePlan capacityLarge (by rw [domain]; exact growDomain)
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits lookupOther otherJournalOutside separate beforeKeys beforeValues
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "old",state.locals.lookup (ofString "old"))}
  refine ⟨restored,?_,?_,?_,?_,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [lookupRun,run]
  · rcases cases with unchanged | grown
    · obtain ⟨nextCount,counts,valid,otherValid⟩ := unchanged
      exact Or.inl ⟨nextCount,counts,valid.after_read post restored keyLength table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl,
        otherValid.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl⟩
    · exact Or.inr ⟨grown.1.after_read post restored keyLength table (allocationEnd pointer keyLength) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer keyLength) capacity stride)
        (htabGrowValues (allocationEnd pointer keyLength) capacity stride) (htabGrowOrder (allocationEnd pointer keyLength) capacity stride) (htabGrowOrderPos (allocationEnd pointer keyLength) capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer keyLength) capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl,
        grown.2.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer keyLength) capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl⟩
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady.jset_supported_with_other_safe_plan
end InitECandidate.Runtime
