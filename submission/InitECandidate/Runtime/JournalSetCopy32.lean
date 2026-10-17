import InitECandidate.Runtime.HashTableReadyMemcpy32
import InitECandidate.Runtime.JournalRecordScopeReady32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original jset copy call reaches its exact record-writing continuation
with the reusable table invariant and at most 33 source-clock steps. -/
theorem HashTableReady32.jset_copy {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (outside : savedKey.toNat + 32 ≤ table.toNat ∨ orderPos.toNat + capacity.toNat * 8 ≤ savedKey.toNat) :
    ∃ post, HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      state.clock ≤ post.clock + 33 ∧ post.clock ≤ state.clock ∧ post.globals = state.globals ∧
      post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be ∧ post.locals = state.locals ∧
      evaluateHOLFiniteState state journalSetCopy32 =
        evaluateHOLFiniteState post
          (.dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
            .panop .mul [.var .global (ofString "journal_n"),.const 32]]) (journalRecordSource32 journalSetFinish32)) := by
  have arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "kc"),.var .local (ofString "key"),.var .local (ofString "klen")] =
      some [.val (.word savedKey),.val (.word key),.val (.word (32 : BitVec 64))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,kc,keyLocal,klen]
  obtain ⟨post,run,postReady,cost,remaining,globals,code,domain,endian,locals⟩ :=
    ready.memcpy_outside state table pointer keys stride capacity used values order orderPos items bits
      (.var .local (ofString "kc")) (.var .local (ofString "key")) (.var .local (ofString "klen")) savedKey key 32
      small aligned sourceAligned budget wordDomain byteDomain sourceWordDomain sourceByteDomain outside arguments
  refine ⟨post,postReady,cost,remaining,globals,code,domain,endian,locals,?_⟩
  unfold journalSetCopy32
  exact evaluate_seq_none run rfl

#print axioms HashTableReady32.jset_copy
end InitECandidate.Runtime
