import InitECandidate.Runtime.MainDecoderEntryFields
import InitECandidate.Runtime.MainStatelessCallNormalResult
import InitECandidate.Runtime.StatelessBodyFinalHeapCells
import InitECandidate.Runtime.StatelessReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- A normal handled decoder call binds the actual decoded structure in main
and preserves its transaction slices and execution-linked final heap. -/
theorem main_decoder_call_returned {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,post)) :
    ∃ length heap : BitVec 64, length.toNat ≤ 134217712 ∧
      ready.locals.lookup (ofString "inp") =
        some (.rStruct [.val (.word 2713731432),.val (.word length)]) ∧
      post.locals = ready.locals.update (ofString "si",.val (.word heap)) ∧
      StatelessReturned ready 2713731432 length 2713715344 heap (.val (.word heap)) post ∧
      ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
        ∀ payload : BitVec 64, post.memory (heap + 0) = .word payload →
          payload.toNat + 136 ≤ finalHeap.toNat ∧
          ∀ array count : BitVec 64, post.memory (payload + 32) = .word array →
            post.memory (payload + 40) = .word count → array.toNat + count.toNat * 16 ≤ finalHeap.toNat := by
  obtain ⟨length,_,_,heap,inp,_,_,small,fits,offsets,atHeap,capped,aligned,lower,installed,domain,_,_⟩ := valid.fields
  obtain ⟨value,bodyPost,bodyRun,_,resumed⟩ :=
    main_stateless_call_normal_result ready post 2713731432 length inp (installed.trans code) run
  let entry := callEntryStateHOLFinite ready (statelessInputCallee 2713731432 length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word 2713731432)) := by
    simp [entry,statelessInputCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,statelessInputCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have cells : ∀ offset ∈ ([0,8,16,24] : List (BitVec 64)),
      entry.memaddrs ((2713715344 : BitVec 64) + offset) := by
    intro offset member
    change ready.memaddrs _
    rw [domain]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals exact arena _ (by decide) (by decide) (by decide)
  have result := stateless_body_returned_final_heap_cells entry bodyPost 2713731432 length 2713715344 heap value
    (installed.trans code) p len offsets atHeap capped aligned
    (by intro address cellAligned lo hi; change ready.memaddrs address; rw [domain];
        exact arena address cellAligned (by omega) hi)
    ⟨cells 0 (by simp),cells 8 (by simp),cells 16 (by simp),cells 24 (by simp)⟩
    (by change 2713715344 + 40 ≤ heap.toNat; omega)
    (by change 2713731432 + length.toNat < 2 ^ 64; exact fits) bodyRun
  have decoded : StatelessReturned ready 2713731432 length 2713715344 heap value bodyPost := result.1
  have valueEq := decoded.1
  have memory : post.memory = bodyPost.memory := by rw [resumed]; rfl
  have globals : post.globals = bodyPost.globals := by rw [resumed]; rfl
  have addresses : post.memaddrs = bodyPost.memaddrs := by rw [resumed]; rfl
  obtain ⟨finalHeap,binding,geometry⟩ := result.2
  refine ⟨length,heap,small,inp,?_,?_,finalHeap,?_,?_⟩
  · rw [resumed,valueEq]
    rfl
  · rw [← valueEq]
    exact decoded.after_frame ready bodyPost post 2713731432 length 2713715344 heap value
      memory globals addresses
  · rw [globals]
    exact binding
  · simpa only [memory] using geometry

#print axioms main_decoder_call_returned
end InitECandidate.Runtime
