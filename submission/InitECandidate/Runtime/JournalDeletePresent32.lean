import InitECandidate.Runtime.JournalDeleteAllocationBody32
import InitECandidate.Runtime.JournalDeleteGuard32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original journal-writing deletion branch under a successful guard. -/
theorem HashTableReady32.jdel_present {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    ∃ post, evaluateHOLFiniteState state journalDeletePresent32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer 32) post) ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 37 ∧ post.clock ≤ state.clock ∧
      post.globals.lookup (ofString "journal_n") = some (.val (.word (count + 1))) ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  let entered := setVarHOLFinite (ofString "klen") (.val (.word (32 : BitVec 64))) state
  have entryReady := ready.after_read state entered table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl
  have locals : ∀ name, name ≠ ofString "klen" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have klen : entered.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨post,run,⟨remaining,counts,postReady⟩,cost,remainingClock,counter,code,domain,endian⟩ :=
    entryReady.jdel_allocation_body entered table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue bits
      ((locals (ofString "key") (by decide)).trans keyLocal) request klen sourceAligned budget
      wordDomain byteDomain sourceWordDomain sourceByteDomain
      ((locals (ofString "t") (by decide)).trans t) ((locals (ofString "old") (by decide)).trans old)
      journalGlobal countGlobal inside journalBound journalAligned journalOutside journalDomain
  have guard := evaluate_journalDelete_guard32 state table count journalCapacity t countGlobal capacityGlobal inside
    (ready.live.arrays.header_domain state table keys stride capacity used values order orderPos items bits 0 (by decide)) ready.live.arrays.cell0
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "klen",state.locals.lookup (ofString "klen"))}
  refine ⟨restored,?_,⟨remaining,counts,postReady.after_read post restored table keys stride capacity used values order orderPos remaining bits
    (allocationEnd pointer 32) rfl rfl rfl rfl rfl⟩,cost,remainingClock,counter,code,domain,endian⟩
  rw [guard]
  change (let output := evaluateHOLFiniteState entered (.decCall (ofString "kc") .one (ofString "alloc") [.var .local (ofString "klen")] journalDeleteCopy32); _) = _
  rw [run]

#print axioms HashTableReady32.jdel_present
end InitECandidate.Runtime
