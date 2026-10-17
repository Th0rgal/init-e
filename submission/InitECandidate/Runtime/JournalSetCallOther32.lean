import InitECandidate.Runtime.JournalSetBodyOther32
import InitECandidate.Runtime.OriginalJournalSetCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original jset call, including call entry and caller-local restoration. -/
theorem HashTableReady32.jset_call_with_other_safe_plan {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (ticks : 5 * capacity.toNat + 2 * (capacity * 2).toNat + 83 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (inside : count.toNat < journalCapacity.toNat)
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)
    (strideBound : stride.toNat ≤ 56) (safePlan : AllocationPlanSafe (allocationEnd pointer 32) (htabGrowAllocationSizes capacity stride))
    (capacityLarge : 1 < capacity.toNat)
    (growDomain : ∀ address : BitVec 64, table.toNat ≤ address.toNat →
      address.toNat < (htabGrowOrderPos (allocationEnd pointer 32) capacity stride).toNat + (capacity * 2).toNat * 8 → state.memaddrs address)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separate : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat ∨ table.toNat + 72 ≤ otherTable.toNat)
    (beforeKeys : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ keys.toNat)
    (beforeValues : otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ values.toNat) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument]) = (none,post) ∧
      ((∃ nextCount : BitVec 64, (nextCount = items ∨ nextCount = items + 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer 32) post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer 32) post) ∨ (HashTableReady32 table (allocationEnd pointer 32) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer 32) capacity stride)
        (htabGrowValues (allocationEnd pointer 32) capacity stride) (htabGrowOrder (allocationEnd pointer 32) capacity stride) (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) post ∧
        HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) post)) ∧
      state.clock ≤ post.clock + 5 * capacity.toNat + 2 * (capacity * 2).toNat + 83 + items.toNat * ((capacity * 2).toNat + 36) ∧
      post.clock ≤ state.clock ∧ post.locals = state.locals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update
      (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  have vt : ofString "value" ≠ ofString "t" := by decide
  have vk : ofString "value" ≠ ofString "key" := by decide
  have kt : ofString "key" ≠ ofString "t" := by decide
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vt,kt]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,vk]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryReady := ready.after_read state entry table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have entryOther := otherReady.after_read state entry otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl
  obtain ⟨post,body,cases,cost,remaining,code,domain,endian⟩ :=
    entryReady.jset_with_other_safe_plan entry table pointer keys stride capacity used values order orderPos items key journal count journalCapacity value bits
      k request sourceAligned (by change 5 * capacity.toNat + 2 * (capacity * 2).toNat + 82 + items.toNat * ((capacity * 2).toNat + 36) ≤ state.clock - 1; omega)
      wordDomain byteDomain sourceWordDomain sourceByteDomain t journalGlobal countGlobal capacityGlobal
      inside journalBound journalAligned journalOutside journalDomain v strideBound safePlan capacityLarge growDomain
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits entryOther otherJournalOutside separate beforeKeys beforeValues
  have installed : state.code.lookup (ofString "jset") =
      some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_jset,.one) := by
    rw [ready.live.arrays.code]; exact originalRuntimeCode_journalSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "jset") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_jset) table key value (by decide) (by decide) (by decide) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "jset")
    [tableArgument,keyArgument,valueArgument] [.val (.word table),.val (.word key),.val (.word value)]
    (sourceFunctionBody Guest.guestFn_jset) callee .one (.val (.word 0)) post arguments lookup (by omega) body
    (by simp [shapeOfHOLExact,shapeEqHOL])
  let restored := {post with locals := state.locals}
  refine ⟨restored,call,?_,?_,?_,rfl,code,domain,endian⟩
  · rcases cases with unchanged | grown
    · obtain ⟨nextCount,counts,valid,otherValid⟩ := unchanged
      exact Or.inl ⟨nextCount,counts,valid.after_read post restored table keys stride capacity used values order orderPos nextCount bits (allocationEnd pointer 32) rfl rfl rfl rfl rfl,
        otherValid.after_read post restored otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer 32) rfl rfl rfl rfl rfl⟩
    · exact Or.inr ⟨grown.1.after_read post restored table (allocationEnd pointer 32) stride (capacity * 2) (htabGrowUsed (allocationEnd pointer 32) capacity stride)
        (htabGrowValues (allocationEnd pointer 32) capacity stride) (htabGrowOrder (allocationEnd pointer 32) capacity stride) (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) (items + 1) (bits + 1)
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl,
        grown.2.after_read post restored otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits
        (allocationEnd (htabGrowOrderPos (allocationEnd pointer 32) capacity stride) ((capacity * 2) * 8)) rfl rfl rfl rfl rfl⟩
  · dsimp only [restored]
    change state.clock - 1 ≤ post.clock + 5 * capacity.toNat + 2 * (capacity * 2).toNat + 82 + items.toNat * ((capacity * 2).toNat + 36) at cost
    omega
  · change post.clock ≤ state.clock
    change post.clock ≤ state.clock - 1 at remaining
    omega

#print axioms HashTableReady32.jset_call_with_other_safe_plan
end InitECandidate.Runtime
