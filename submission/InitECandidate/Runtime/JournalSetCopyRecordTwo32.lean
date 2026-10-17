import InitECandidate.Runtime.JournalRecordScopeTwo32
import InitECandidate.Runtime.JournalSetCopyTwo32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose the original copy and record-writing stages into the final suffix. -/
theorem HashTableReady32.jset_copy_record_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items savedKey key journal count journalCapacity present oldValue : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word savedKey)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (klen : state.locals.lookup (ofString "klen") = some (.val (.word (32 : BitVec 64))))
    (small : savedKey.toNat + 32 ≤ 33806089496)
    (aligned : savedKey.toNat % 8 = 0) (sourceAligned : key.toNat % 8 = 0) (budget : 33 ≤ state.clock)
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
      address.toNat < journal.toNat + journalCapacity.toNat * 32 → state.memaddrs address)
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherOutside : savedKey.toNat + 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ savedKey.toNat)
    (otherJournalOutside : journal.toNat + journalCapacity.toNat * 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ journal.toNat) :
    ∃ post, HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + 33 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "r" → post.locals.lookup name = state.locals.lookup name) ∧
      evaluateHOLFiniteState state journalSetCopy32 =
        (let output := evaluateHOLFiniteState post journalSetFinish32;
          (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals (ofString "r",state.locals.lookup (ofString "r")))})) := by
  obtain ⟨copied,copyReady,copyOther,cost,remaining,globals,code,domain,endian,locals,copyRun⟩ :=
    ready.jset_copy_with_other state table pointer keys stride capacity used values order orderPos items savedKey key bits
      kc keyLocal klen small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain outside
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady otherOutside
  obtain ⟨post,postReady,postOther,clock,postGlobals,postCode,postDomain,postEndian,postLocals,recordRun⟩ :=
    copyReady.journal_scope_with_other copied table pointer keys stride capacity used values order orderPos items journal count journalCapacity savedKey present oldValue bits
      (by rw [locals]; exact t) (by rw [locals]; exact kc) (by rw [locals]; exact old)
      (by rw [globals]; exact journalGlobal) (by rw [globals]; exact countGlobal)
      inside journalBound journalAligned journalOutside (by rw [domain]; exact journalDomain)
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits copyOther otherJournalOutside
  refine ⟨post,postReady,postOther,?_,?_,postGlobals.trans globals,postCode.trans code,postDomain.trans domain,postEndian.trans endian,?_,?_⟩
  · omega
  · omega
  · intro name different
    exact (postLocals name different).trans (congrArg (fun map => map.lookup name) locals)
  · rw [copyRun,recordRun journalSetFinish32,locals]

#print axioms HashTableReady32.jset_copy_record_with_other
end InitECandidate.Runtime
