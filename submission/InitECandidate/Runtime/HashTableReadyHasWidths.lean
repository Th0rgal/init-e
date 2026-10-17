import InitECandidate.Runtime.HashTableReady
import InitECandidate.Runtime.HashHasBodyWidths
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableReady.has20 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (ready : HashTableReady 20 table keys stride capacity used values order orderPos items bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (20 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_has) =
        (some (.returned (.val (.word value))),post) ∧
      HashTableReady 20 table keys stride capacity used values order orderPos items bits pointer post ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨value,post,boolean,run,cost,remaining,memory,globals,code,domain,endian⟩ :=
    evaluate_source_hashHas20 state table keys stride capacity used values order orderPos items key bits
      ready.live.arrays tableLocal keyLocal keyAligned keyWords keyBytes budget
  exact ⟨value,post,boolean,run,
    HashTableReady.after_read state post 20 table keys stride capacity used values order orderPos items bits pointer ready memory globals code domain endian,
    cost,remaining,memory,globals,code,domain,endian⟩


theorem HashTableReady.has52 {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (ready : HashTableReady 52 table keys stride capacity used values order orderPos items bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (52 : BitVec 64).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_has) =
        (some (.returned (.val (.word value))),post) ∧
      HashTableReady 52 table keys stride capacity used values order orderPos items bits pointer post ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨value,post,boolean,run,cost,remaining,memory,globals,code,domain,endian⟩ :=
    evaluate_source_hashHas52 state table keys stride capacity used values order orderPos items key bits
      ready.live.arrays tableLocal keyLocal keyAligned keyWords keyBytes budget
  exact ⟨value,post,boolean,run,
    HashTableReady.after_read state post 52 table keys stride capacity used values order orderPos items bits pointer ready memory globals code domain endian,
    cost,remaining,memory,globals,code,domain,endian⟩


#print axioms HashTableReady.has20
#print axioms HashTableReady.has52
end InitECandidate.Runtime
