import InitECandidate.Runtime.HashTableLiveLinkedEntriesSet32
import InitECandidate.Runtime.HashTableLiveDelete32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Shared state carried between mixed set and delete operations. -/
structure HashTableReady32 {F : Type}
    (table keys stride capacity used values order orderPos items : BitVec 64)
    (bits : Nat) (pointer : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  live : HashTableLive32 table keys stride capacity used values order orderPos items bits pointer state
  valuesWord : HashValueEntriesWord used values capacity state
  reverse : HashReverseEntriesBound used orderPos capacity items state
  linked : HashOrderLinked used order orderPos capacity items state
  ordering : keys.toNat + capacity.toNat * stride.toNat ≤ values.toNat

 theorem HashTableReady32.after_read {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos items : BitVec 64)
    (bits : Nat) (pointer : BitVec 64)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (memory : post.memory = state.memory) (globals : post.globals = state.globals)
    (code : post.code = state.code) (domain : post.memaddrs = state.memaddrs) (endian : post.be = state.be) :
    HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post := by
  exact ⟨⟨ready.live.arrays.after_read state post table keys stride capacity used values order orderPos items bits memory code domain endian,
    ready.live.entries.after_memory state post order capacity items memory,
    ready.live.frontier.after_globals state post orderPos capacity pointer globals⟩,
    ready.valuesWord.after_read state post used values capacity memory domain endian,
    ready.reverse.after_read state post used orderPos capacity items memory domain endian,
    ready.linked.after_read state post used order orderPos capacity items memory domain endian,ready.ordering⟩

theorem HashTableReady32.delete_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : capacity.toNat * 37 + 3 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htab_del") [tableArgument,keyArgument]) = (none,post) ∧
      (∃ remaining : BitVec 64, (remaining = items ∨ remaining = items - 1) ∧
        HashTableReady32 table keys stride capacity used values order orderPos remaining bits pointer post) ∧
      state.clock ≤ post.clock + capacity.toNat * 37 + 3 ∧ post.clock ≤ state.clock ∧
      post.locals = state.locals ∧ post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,⟨count,counts,live,words,reverse,linked⟩,cost,remaining,locals,globals,code,domain,endian⟩ :=
    ready.live.delete_call_all state table pointer keys stride capacity used values order orderPos items key bits
      ready.valuesWord ready.reverse ready.linked ready.ordering tableArgument keyArgument arguments keyAligned keyDomain budget
  exact ⟨post,run,⟨count,counts,⟨live,words,reverse,linked,ready.ordering⟩⟩,cost,remaining,locals,globals,code,domain,endian⟩

#print axioms HashTableReady32.after_read
#print axioms HashTableReady32.delete_call
end InitECandidate.Runtime
