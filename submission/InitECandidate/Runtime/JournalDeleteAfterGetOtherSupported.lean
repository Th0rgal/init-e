import InitECandidate.Runtime.JournalDeletePresentOtherSupported
import InitECandidate.Runtime.JournalDeleteAbsent32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both lookup outcomes of the original journal deletion continuation. -/
theorem HashTableReady.jdel_after_get_supported_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    ∃ post, evaluateHOLFiniteState state journalDeleteAfterGet32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post) ∨
       (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady keyLength table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer keyLength) post ∧
        HashTableReady otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits (allocationEnd pointer keyLength) post)) ∧
      state.clock ≤ post.clock + capacity.toNat * 57 + keyLength.toNat + 5 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  by_cases absent : present = 0
  · have run := evaluate_journalDelete_absent32 state oldValue (by simpa [absent] using old)
    exact ⟨emptyLocalsHOLFinite state,run,Or.inl ⟨ready.after_read state _ keyLength table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl,
      otherReady.after_read state _ otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer rfl rfl rfl rfl rfl⟩,
      by change state.clock ≤ state.clock + capacity.toNat * 57 + keyLength.toNat + 5; omega,by simp [emptyLocalsHOLFinite],rfl,rfl,rfl⟩
  · have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      have notZero : present ≠ (0#64) := absent
      simp [evalHOLExact,old,Compiler.Encoders.Asm.wordCmpHOL,notZero]
    have guard : evaluateHOLFiniteState state
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) (.return (.const 0)) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    obtain ⟨post,run,⟨count,counts,target⟩,preserved,cost,remaining,_,code,domain,endian⟩ :=
      ready.jdel_present_supported_with_other state keyLength table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue bits supported
        keyLocal request sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
        t old journalGlobal countGlobal capacityGlobal inside journalBound journalAligned journalOutside journalDomain
        otherKeyLength otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady otherJournalOutside separated
    exact ⟨post,evaluate_seq_none guard run,Or.inr ⟨count,counts,target,preserved⟩,cost,remaining,code,domain,endian⟩

#print axioms HashTableReady.jdel_after_get_supported_with_other
end InitECandidate.Runtime
