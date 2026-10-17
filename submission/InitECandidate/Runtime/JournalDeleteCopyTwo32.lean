import InitECandidate.Runtime.HashTableReadyMemcpyTwo32
import InitECandidate.Runtime.JournalDeleteScopeReady32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original jset copy call reaches its exact record-writing continuation
with the reusable table invariant and at most 33 source-clock steps. -/
theorem HashTableReady32.jdel_copy_with_other {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items savedKey key : BitVec 64) (bits : Nat)
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
    (otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems : BitVec 64) (otherBits : Nat)
    (otherReady : HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer state)
    (otherOutside : savedKey.toNat + 32 ≤ otherTable.toNat ∨ otherOrderPos.toNat + otherCapacity.toNat * 8 ≤ savedKey.toNat) :
    ∃ post, HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      HashTableReady32 otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits pointer post ∧
      state.clock ≤ post.clock + 33 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      evaluateHOLFiniteState state journalDeleteCopy32 =
        evaluateHOLFiniteState post
          (.dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
            .panop .mul [.var .global (ofString "journal_n"),.const 32]]) (journalDeleteRecordSource32 journalDeleteFinish32)) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "kc"),.var .local (ofString "key"),.var .local (ofString "klen")] =
      some [.val (.word savedKey),.val (.word key),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,kc,keyLocal,klen]
  obtain ⟨post,run,postReady,preserved,cost,remaining,globals,code,domain,endian,locals⟩ :=
    ready.memcpy_with_other state table pointer keys stride capacity used values order orderPos items bits
      (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen")) savedKey key 32
      small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain outside arguments
      otherTable otherKeys otherStride otherCapacity otherUsed otherValues otherOrder otherOrderPos otherItems otherBits otherReady otherOutside
  refine ⟨post,postReady,preserved,cost,remaining,globals,code,domain,endian,locals,?_⟩
  unfold journalDeleteCopy32
  exact evaluate_seq_none run rfl

#print axioms HashTableReady32.jdel_copy_with_other
end InitECandidate.Runtime
