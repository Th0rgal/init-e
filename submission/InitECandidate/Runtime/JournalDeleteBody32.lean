import InitECandidate.Runtime.JournalDeleteAfterGet32
import InitECandidate.Runtime.JournalDeleteLookup32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Complete original journal deletion, including both lookup outcomes. -/
theorem HashTableReady32.jdel_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key journal count journalCapacity : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (request : (32 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (sourceAligned : key.toNat % 8 = 0) (budget : capacity.toNat * 39 + 40 ≤ state.clock)
    (wordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (pointer + BitVec.ofNat 64 offset)))
    (sourceWordDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (sourceByteDomain : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word journalCapacity)))
    (inside : count.toNat < journalCapacity.toNat)
    (journalBound : journal.toNat + journalCapacity.toNat * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat)
    (journalDomain : ∀ address : BitVec 64, journal.toNat ≤ address.toNat →
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address) :
    ∃ post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel) =
      (some (.returned (.val (.word (0 : BitVec 64)))),post) ∧
      ((HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post) ∨
       (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits (allocationEnd pointer 32) post)) ∧
      state.clock ≤ post.clock + capacity.toNat * 39 + 40 ∧ post.clock ≤ state.clock ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word key)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,t,keyLocal]
  have keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset) := by
    intro offset member
    apply sourceWordDomain
    simp at member
    omega
  obtain ⟨present,oldValue,looked,_,lookupReady,old,lookupCost,lookupRemaining,memory,globals,code,domain,endian,locals,lookupRun⟩ :=
    ready.jdel_lookup state table pointer keys stride capacity used values order orderPos items key bits arguments sourceAligned keyDomain (by omega)
  obtain ⟨post,run,cases,cost,remaining,postCode,postDomain,postEndian⟩ :=
    lookupReady.jdel_after_get looked table pointer keys stride capacity used values order orderPos items key journal count journalCapacity present oldValue bits
      ((locals (ofString "key") (by decide)).trans keyLocal) request sourceAligned (by omega)
      (by rw [domain]; exact wordDomain) (by rw [domain]; exact byteDomain)
      (by rw [domain]; exact sourceWordDomain) (by rw [domain]; exact sourceByteDomain)
      ((locals (ofString "t") (by decide)).trans t) old
      (by rw [globals]; exact journalGlobal) (by rw [globals]; exact countGlobal) (by rw [globals]; exact capacityGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
  let restored := {post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "old",state.locals.lookup (ofString "old"))}
  refine ⟨restored,?_,?_,?_,?_,postCode.trans code,postDomain.trans domain,postEndian.trans endian⟩
  · rw [lookupRun,run]
  · rcases cases with unchanged | deleted
    · exact Or.inl (unchanged.after_read post restored table keys stride capacity used values order orderPos items bits pointer rfl rfl rfl rfl rfl)
    · obtain ⟨remaining,counts,valid⟩ := deleted
      exact Or.inr ⟨remaining,counts,valid.after_read post restored table keys stride capacity used values order orderPos remaining bits
        (allocationEnd pointer 32) rfl rfl rfl rfl rfl⟩
  · dsimp only [restored]
    omega
  · change post.clock ≤ state.clock
    omega

#print axioms HashTableReady32.jdel_body
end InitECandidate.Runtime
