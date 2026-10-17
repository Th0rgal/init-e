import InitECandidate.Runtime.JournalDeleteAfterGetOtherSupported
import InitECandidate.Runtime.JournalDeleteLookupSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original journal deletion, including both lookup outcomes. -/
theorem HashTableReady.jdel_body_supported_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : keyLength ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 59 + keyLength.toNat + 8 ≤ state.clock)
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
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨
       (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer keyLength) post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) post)) ∧
      state.clock ≤ post.clock + capacity.toNat * 59 + keyLength.toNat + 8 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,keyLocal]
  obtain ⟨present,oldValue,looked,_,lookupReady,old,lookupCost,lookupRemaining,memory,globals,code,domain,endian,locals,lookupRun⟩ :=
    ready.jdel_lookup_supported state keyLength table pointer keys stride capacity used values order orderPos items key bits supported arguments sourceAligned sourceWordDomain sourceByteDomain (by omega)
  have lookupOther := otherReady.after_read state looked otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer memory globals code domain endian
  obtain ⟨post,run,cases,cost,remaining,postCode,postDomain,postEndian⟩ :=
    lookupReady.jdel_after_get_supported_with_other looked keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue bits supported
      ((locals (ofString "key") (by decide)).trans keyLocal) request sourceAligned (by omega)
      (by rw [domain]; exact wordDomain) (by rw [domain]; exact byteDomain)
      (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      ((locals (ofString "t") (by decide)).trans t) old
      (by rw [globals]; exact journalGlobal) (by rw [globals]; exact countGlobal) (by rw [globals]; exact capacityGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits lookupOther otherJournalOutside separated
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "old",state.locals.lookup (ofString "old"))}
  refine ⟨restored,?_,?_,?_,?_,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [lookupRun,run]
  · rcases cases with ⟨unchanged,otherUnchanged⟩ | deleted
    · exact Or.inl ⟨unchanged.after_read post restored keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl,
        otherUnchanged.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl⟩
    · obtain ⟨remaining,counts,valid,otherValid⟩ := deleted
      exact Or.inr ⟨remaining,counts,valid.after_read post restored keyLength table keys stride capacity used values order orderPos remaining bits
        (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl,
        otherValid.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl⟩
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady.jdel_body_supported_with_other
end InitECandidate.Runtime
