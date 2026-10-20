import InitECandidate.Runtime.MainDecoderEntryHeapUpper
import InitECandidate.Runtime.MainStatelessCallNormalResult
import InitECandidate.Runtime.StatelessBodyHeapUpper
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The actual initialization/input/buffer chain and successful handled source
stateless decoder call leave the persistent heap below five billion bytes.
No initial-heap upper bound is assumed. -/
theorem main_decoder_call_heap_upper {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code=originalRuntimeCode)
    (arena : ∀address : BitVec 64,address.toNat%8=0→2713714688≤address.toNat→address.toNat<33806089496→state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall=(none,post)) :
    ∃ length initialHeap finalHeap : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr")=some (.val (.word initialHeap)) ∧length.toNat≤134217712 ∧
      ready.locals.lookup (ofString "inp")=some (.rStruct [.val (.word 2713731432),.val (.word length)]) ∧
      initialHeap.toNat≤2713731432+length.toNat+320 ∧
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word finalHeap)) ∧initialHeap.toNat≤finalHeap.toNat ∧
      finalHeap.toNat≤2713731432+17*length.toNat+720 ∧finalHeap.toNat≤5000000000 ∧finalHeap.toNat≤33805929128 := by
  obtain ⟨length,_,_,heap,inp,_,_,small,fits,offsets,atHeap,capped,aligned,lower,installed,domain,_,_,initialUpper⟩ := valid.fields_heap_upper
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
  obtain ⟨finalHeap,binding,lowerFinal,upperFinal⟩:=decode_stateless_input_returned_heap_upper entry bodyPost 2713731432 length 2713715344 heap value
    (installed.trans code) p len offsets atHeap capped aligned
    (by intro address cellAligned lo hi;change ready.memaddrs address;rw [domain];exact arena address cellAligned (by omega) hi)
    ⟨cells 0 (by simp),cells 8 (by simp),cells 16 (by simp),cells 24 (by simp)⟩
    (by change 2713715344+40≤heap.toNat;omega)
    (by change 2713731432+length.toNat<2^64;exact fits) bodyRun
  have globals : post.globals=bodyPost.globals := by rw [resumed];rfl
  exact ⟨length,heap,finalHeap,atHeap,small,inp,initialUpper,by rw [globals];exact binding,lowerFinal,by omega,by omega,by omega⟩
#print axioms main_decoder_call_heap_upper
end InitECandidate.Runtime
