import InitECandidate.Runtime.JournalDeletePresent32
import InitECandidate.Runtime.JournalDeleteAbsent32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both lookup outcomes of the original journal deletion continuation. -/
theorem HashTableReady32.jdel_after_get {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 37 + 37 ≤ state.clock)
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
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state journalDeleteAfterGet32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post) ∨
       (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer 32) post)) ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 37 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  by_cases absent : present = 0
  · have run := evaluate_journalDelete_absent32 state oldValue (by simpa [absent] using old)
    exact ⟨emptyLocalsHOLFinite state,run,Or.inl (ready.after_read state _ table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl),
      by change state.clock ≤ state.clock + capacity.toNat * 37 + 37; omega,by simp [emptyLocalsHOLFinite],rfl,rfl,rfl⟩
  · have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
      have notZero : present ≠ (0#64) := absent
      simp [evalHOLExact,old,Compiler.Encoders.Asm.wordCmpHOL,notZero]
    have guard : evaluateHOLFiniteState state
        (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "old"))) (.const 0)) (.return (.const 0)) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [evaluateHOLFiniteState_skip]
    obtain ⟨post,run,valid,cost,remaining,_,code,domain,endian⟩ :=
      ready.jdel_present state table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue bits
        keyLocal request sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain
        t old journalGlobal countGlobal capacityGlobal inside journalBound journalAligned journalOutside journalDomain
    exact ⟨post,evaluate_seq_none guard run,Or.inr valid,cost,remaining,code,domain,endian⟩

#print axioms HashTableReady32.jdel_after_get
end InitECandidate.Runtime
