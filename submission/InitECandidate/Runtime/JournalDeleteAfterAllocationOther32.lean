import InitECandidate.Runtime.JournalDeleteCopyRecordTwo32
import InitECandidate.Runtime.JournalDeleteFinishOther32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original journal deletion body after key-copy allocation. -/
theorem HashTableReady32.jdel_after_allocation_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (small : savedKey.toNat + 32 ≤ 33806089496)
    (aligned : savedKey.toNat % 8 = 0) (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 37 + 36 ≤ state.clock)
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
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherOutside : savedKey.toNat + 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ savedKey.toNat)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state journalDeleteCopy32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 36 ∧ post.clock ≤ state.clock ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨recorded,recordReady,recordOther,copyCost,copyRemaining,globals,code,domain,endian,locals,copyRun⟩ :=
    ready.jdel_copy_record_with_other state table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue bits
      kc keyLocal klen small aligned sourceAligned (by omega) wordDomain byteDomain sourceWordDomain sourceByteDomain outside
      t old journalGlobal countGlobal inside journalBound journalAligned journalOutside journalDomain
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady otherOutside otherJournalOutside
  have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), recorded.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    rw [domain]
    apply sourceWordDomain
    simp at member
    omega
  obtain ⟨post,run,⟨remaining,counts,postReady⟩,preserved,cost,remainingClock,counter,postCode,postDomain,postEndian⟩ :=
    recordReady.jdel_finish_with_other recorded table pointer keys stride capacity used values order orderPos items key count bits
      ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "key") (by decide)).trans keyLocal)
      (by rw [globals]; exact countGlobal) sourceAligned keyDomain
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits recordOther separated (by omega)
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "r",state.locals.lookup (ofString "r"))}
  refine ⟨restored,?_,⟨remaining,counts,postReady.after_read post restored table keys stride capacity used values order orderPos remaining bits pointer
    rfl rfl rfl rfl rfl⟩,preserved.after_read post restored otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl,?_,?_,counter,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [copyRun,run]
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady32.jdel_after_allocation_with_other
end InitECandidate.Runtime
