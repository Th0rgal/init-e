import InitECandidate.Runtime.HashTableReady
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem HashTableLive.alloc_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64)
    (bits : Nat) (pointer size : BitVec 64) (argument : ExpHOL 64)
    (live : HashTableLive keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word size)])
    (clock : state.clock ≠ 0)
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "alloc") [argument]) = (none,post) ∧
      HashTableLive keyLength table keys stride capacity used values order orderPos count bits
        (allocationEnd pointer size) post ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.eshapes = state.eshapes ∧ post.be = state.be := by
  obtain ⟨post,run,frontier,ticks,memory,locals,code,domain,shapes,endian⟩ :=
    live.frontier.alloc_call state orderPos capacity pointer size argument arguments live.arrays.code clock request
  exact ⟨post,run,⟨live.arrays.after_read state post keyLength table keys stride capacity used values order orderPos count bits
      memory code domain endian,live.entries.after_memory state post order capacity count memory,frontier⟩,
    ticks,memory,locals,code,domain,shapes,endian⟩

theorem HashTableReady.alloc_call {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table keys stride capacity used values order orderPos count : BitVec 64)
    (bits : Nat) (pointer size : BitVec 64) (argument : ExpHOL 64)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos count bits pointer state)
    (arguments : evalListHOLFinite state
      (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
        some [.val (.word size)])
    (clock : state.clock ≠ 0)
    (request : size ≤ (33806089496 : BitVec 64) - pointer) :
    ∃ post, evaluateHOLFiniteState state
        (.call (some (none,none)) (ofString "alloc") [argument]) = (none,post) ∧
      HashTableReady keyLength table keys stride capacity used values order orderPos count bits
        (allocationEnd pointer size) post ∧
      post.clock = state.clock - 1 ∧ post.memory = state.memory ∧
      post.locals = state.locals ∧ post.code = state.code ∧
      post.memaddrs = state.memaddrs ∧ post.eshapes = state.eshapes ∧ post.be = state.be := by
  obtain ⟨post,run,live,ticks,memory,locals,code,domain,shapes,endian⟩ :=
    ready.live.alloc_call state keyLength table keys stride capacity used values order orderPos count bits pointer size argument arguments clock request
  exact ⟨post,run,⟨live,ready.valuesWord.after_read state post used values capacity memory domain endian,
    ready.reverse.after_read state post used orderPos capacity count memory domain endian,
    ready.linked.after_read state post used order orderPos capacity count memory domain endian,ready.ordering⟩,
    ticks,memory,locals,code,domain,shapes,endian⟩

#print axioms HashTableLive.alloc_call
#print axioms HashTableReady.alloc_call
end InitECandidate.Runtime
