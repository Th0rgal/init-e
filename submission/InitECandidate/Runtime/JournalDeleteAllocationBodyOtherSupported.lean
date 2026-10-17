import InitECandidate.Runtime.JournalDeleteAllocateTwoWidth
import InitECandidate.Runtime.JournalDeleteAfterAllocationOtherSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original journal deletion allocation through return, with an advanced heap. -/
theorem HashTableReady.jdel_allocation_body_supported_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : keyLength ≤ (33806089496 : BitVec 64) - pointer)
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word keyLength)))
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 57 + keyLength.toNat + 5 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
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
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ table.toNat) :
    ∃ post, evaluateHOLFiniteState state (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalDeleteCopy32) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer keyLength) post) ∧
      HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) post ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + keyLength.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨allocated,allocatedReady,allocatedOther,kc,locals,globals,clock,memory,code,domain,endian,allocateRun⟩ :=
    ready.jdel_allocate_with_other state keyLength table pointer keys stride capacity used values order orderPos items bits klen (by omega) request
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady
  have small : pointer.toNat + keyLength.toNat ≤ 33806089496 :=
    allocationGuard_sum_bound pointer keyLength ready.live.frontier.bounded request
  obtain ⟨post,run,⟨remaining,counts,postReady⟩,preserved,cost,remainingClock,counter,postCode,postDomain,postEndian⟩ :=
    allocatedReady.jdel_after_allocation_supported_with_other allocated keyLength table (allocationEnd pointer keyLength) keys stride capacity used values order orderPos items pointer key journal count journalCapacity present oldValue bits supported
      kc ((locals (ofString "key") (by decide)).trans keyLocal) ((locals (ofString "klen") (by decide)).trans klen)
      small ready.live.frontier.aligned sourceAligned (by omega)
      (by rw [domain]; exact wordDomain) (by rw [domain]; exact byteDomain)
      (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      (Or.inr ready.live.frontier.allocated) ((locals (ofString "t") (by decide)).trans t)
      ((locals (ofString "old") (by decide)).trans old)
      ((globals (ofString "journal") (by decide)).trans journalGlobal)
      ((globals (ofString "journal_n") (by decide)).trans countGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
      otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits allocatedOther
      (Or.inr otherReady.live.frontier.allocated) otherJournalOutside separated
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "kc",state.locals.lookup (ofString "kc"))}
  refine ⟨restored,?_,⟨remaining,counts,postReady.after_read post restored keyLength table keys stride capacity used values order orderPos remaining bits
    (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl⟩,preserved.after_read post restored otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) rfl rfl rfl rfl rfl,?_,?_,counter,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [allocateRun,run]
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady.jdel_allocation_body_supported_with_other
end InitECandidate.Runtime
