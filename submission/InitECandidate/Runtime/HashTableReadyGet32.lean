import InitECandidate.Runtime.HashTableReady32
import InitECandidate.Runtime.HashTableArraysGet32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Lookup executes the original source body and retains the mixed-operation state. -/
theorem HashTableReady32.get {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table pointer keys stride capacity used values order orderPos items key : BitVec 64) (bits : Nat)
    (ready : HashTableReady32 table keys stride capacity used values order orderPos items bits pointer state)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyDomain : ∀ offset ∈ ([0,8,16,24] : List Nat), state.memaddrs (key + BitVec.ofNat 64 offset))
    (budget : 2 * capacity.toNat + 2 ≤ state.clock) :
    ∃ present value : BitVec 64, ∃ post, (present = 0 ∨ present = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_get) =
        (some (.returned (.rStruct [.val (.word present),.val (.word value)])),post) ∧
      HashTableReady32 table keys stride capacity used values order orderPos items bits pointer post ∧
      state.clock ≤ post.clock + 2 * capacity.toNat + 2 ∧ post.clock ≤ state.clock ∧
      post.memory = state.memory ∧ post.globals = state.globals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨present,value,post,boolean,run,cost,remaining,memory,globals,code,domain,endian,_⟩ :=
    ready.live.arrays.get state table keys stride capacity used values order orderPos items key bits
      tableLocal keyLocal keyAligned keyDomain budget
  exact ⟨present,value,post,boolean,run,
    ready.after_read state post table keys stride capacity used values order orderPos items bits pointer memory globals code domain endian,
    cost,remaining,memory,globals,code,domain,endian⟩

#print axioms HashTableReady32.get
end InitECandidate.Runtime
