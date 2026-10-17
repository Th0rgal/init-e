import InitECandidate.Runtime.JournalDeleteAllocationBodyOtherSupported
import InitECandidate.Runtime.JournalDeleteGuardWidth
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original journal-writing deletion branch under a successful guard. -/
theorem HashTableReady.jdel_present_supported_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : keyLength ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 57 + keyLength.toNat + 5 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state journalDeletePresent32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer keyLength) post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + keyLength.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "klen") (.val (.word keyLength)) state
  have entryReady := ready.after_read state entered keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have locals : ∀ name, name ≠ ofString "klen" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have klen : entered.locals.lookup (ofString "klen") = some (.val (.word keyLength)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryOther := otherReady.after_read state entered otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl
  obtain ⟨post,run,⟨remaining,counts,postReady⟩,preserved,cost,remainingClock,counter,code,domain,endian⟩ :=
    entryReady.jdel_allocation_body_supported_with_other entered keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue bits supported
      ((locals (ofString "key") (by decide)).trans keyLocal) request klen sourceAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain
      ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "old") (by decide)).trans old)
      journalGlobal countGlobal inside journalBound journalAligned journalOutside journalDomain
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits entryOther otherJournalOutside separated
  have guard := evaluate_journalDelete_guard_width state keyLength table count journalCapacity t countGlobal capacityGlobal inside
    (ready.live.arrays.header_domain state keyLength table keys stride capacity used values order orderPos items bits 0 (by decide)) ready.live.arrays.cell0
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "klen",state.locals.lookup (ofString "klen"))}
  refine ⟨restored,?_,⟨remaining,counts,postReady.after_read post restored keyLength table keys stride capacity used values order orderPos remaining bits
    (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl⟩,preserved.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl,cost,remainingClock,counter,code,domain,endian⟩
  rw [guard]
  change (let output := evaluateHOLFiniteState entered (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalDeleteCopy32); _) = _
  rw [run]

#print axioms HashTableReady.jdel_present_supported_with_other
end InitECandidate.Runtime
