import InitECandidate.Runtime.MainDecoderEntryFields
import InitECandidate.Runtime.MainStatelessCallNormalResult
import InitECandidate.Runtime.StatelessBodyReturnedRequestsLinked
import InitECandidate.Runtime.HtrNewPayloadAllocationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Main's actual handled decoder call exports the complete payload hash
metadata on normal completion, using only the concrete aligned arena cells. -/
theorem main_decoder_call_requests_linked {F : Type} (state ready post : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 →
      2713714688 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (valid : MainDecoderEntry state ready)
    (run : evaluateHOLFiniteState ready mainStatelessCall = (none,post)) :
    ∃ length heap record : BitVec 64, length.toNat ≤ 134217712 ∧ heap.toNat + 32 < record.toNat ∧
      post.memaddrs (heap + (32#64)) ∧ post.memory (heap + (32#64)) = .word record ∧ HtrRequestsDecoded post record := by
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
  obtain ⟨record,afterHeap,pointerDomain,pointerCell,decoded⟩ :=
    stateless_body_returned_requests_linked entry bodyPost 2713731432 length 2713715344 heap value
      (installed.trans code) p len offsets atHeap capped aligned
      (by intro address cellAligned lo hi; change ready.memaddrs address; rw [domain];
          exact arena address cellAligned (by omega) hi)
      ⟨cells 0 (by simp),cells 8 (by simp),cells 16 (by simp),cells 24 (by simp)⟩
      (by change 2713715344 + 40 ≤ heap.toNat; omega) (by change 2713731432 + length.toNat < 2 ^ 64; exact fits)
      small bodyRun
  have memory : post.memory = bodyPost.memory := by rw [resumed]; rfl
  have addresses : post.memaddrs = bodyPost.memaddrs := by rw [resumed]; rfl
  exact ⟨length,heap,record,small,afterHeap,by rw [addresses]; exact pointerDomain,
    by rw [memory]; exact pointerCell,decoded.after_frame memory addresses⟩

#print axioms main_decoder_call_requests_linked
end InitECandidate.Runtime
