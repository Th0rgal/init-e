import InitECandidate.Runtime.HashTableAllocationFrontier32
import InitECandidate.Runtime.HashTableArraysRead32
import InitECandidate.Runtime.HashOrderEntriesAppend
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Runtime facts carried for a live table, including relocated arrays. -/
structure HashTableLive32 {F : Type}
    (table keys stride capacity used values order orderPos count : BitVec 64)
    (bits : Nat) (pointer : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Prop where
  arrays : HashTableArraysInvariant32 table keys stride capacity used values order orderPos count bits state
  entries : HashOrderEntriesBound order capacity count state
  frontier : HashTableHeapFrontier32 orderPos capacity pointer state

/-- An actual allocator call preserves all live-table facts together. -/
theorem HashTableLive32.alloc_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (table keys stride capacity used values order orderPos count : BitVec 64)
    (bits : Nat) (pointer size : BitVec 64) (argument : ExpHOL 64)
    (live : HashTableLive32 table keys stride capacity used values order orderPos count bits pointer state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word size)])
    (clock : state.clock ≠ 0)
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "alloc") [argument]) = (none,post) ∧
      HashTableLive32 table keys stride capacity used values order orderPos count bits
        (allocationEnd pointer size) post ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.eshapes = state.eshapes ∧ post.be = state.be := by
  obtain ⟨post,run,frontier,ticks,memory,locals,code,domain,shapes,endian⟩ :=
    live.frontier.alloc_call state orderPos capacity pointer size argument arguments live.arrays.code clock request
  exact ⟨post,run,⟨live.arrays.after_read state post table keys stride capacity used values order orderPos count bits
      memory code domain endian,live.entries.after_memory state post order capacity count memory,frontier⟩,
    ticks,memory,locals,code,domain,shapes,endian⟩

#print axioms HashTableLive32.alloc_call
end InitECandidate.Runtime
