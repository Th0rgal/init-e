import InitECandidate.Runtime.JournalDeleteCopyRecordTwoWidth
import InitECandidate.Runtime.JournalDeleteFinishOtherSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original journal deletion body after key-copy allocation. -/
theorem HashTableReady.jdel_after_allocation_supported_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (small : savedKey.toNat + keyLength.toNat ≤ 33806089496)
    (aligned : savedKey.toNat % 8 = 0) (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 57 + keyLength.toNat + 4 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (savedKey + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (savedKey + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outside : savedKey.toNat + keyLength.toNat ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ savedKey.toNat)
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word oldValue)]))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (inside : count.toNat < journalCapacity.toNat)
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)    (otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherOutside : savedKey.toNat + keyLength.toNat ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ savedKey.toNat)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state journalDeleteCopy32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + keyLength.toNat + 4 ∧ post.clock ≤ state.clock ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨recorded,recordReady,recordOther,copyCost,copyRemaining,globals,code,domain,endian,locals,copyRun⟩ :=
    ready.jdel_copy_record_with_other state keyLength table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue bits
      kc keyLocal klen small aligned sourceAligned (by omega) wordDomain byteDomain sourceWordDomain sourceByteDomain outside
      t old journalGlobal countGlobal inside journalBound journalAligned journalOutside journalDomain
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady otherOutside otherJournalOutside
  obtain ⟨post,run,⟨remaining,counts,postReady⟩,preserved,cost,remainingClock,counter,postCode,postDomain,postEndian⟩ :=
    recordReady.jdel_finish_supported_with_other recorded keyLength table pointer keys stride capacity used values order orderPos items key count bits supported
      ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "key") (by decide)).trans keyLocal)
      (by rw [globals]; exact countGlobal) sourceAligned (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits recordOther separated (by omega)
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "r",state.locals.lookup (ofString "r"))}
  refine ⟨restored,?_,⟨remaining,counts,postReady.after_read post restored keyLength table keys stride capacity used values order orderPos remaining bits pointer
    rfl rfl rfl rfl rfl⟩,preserved.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,?_,?_,counter,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [copyRun,run]
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady.jdel_after_allocation_supported_with_other
end InitECandidate.Runtime
