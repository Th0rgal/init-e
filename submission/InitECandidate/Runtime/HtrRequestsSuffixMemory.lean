import InitECandidate.Runtime.HtrRequestsSuffixBound
import InitECandidate.Runtime.HtrPcontainerMemory
import InitECandidate.Runtime.HtrRequestListMemory
import InitECandidate.Runtime.HeapReleaseMemory
import InitECandidate.Runtime.HtabGrowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def HtrRequestsSuffixMemory (index cost : Nat) : Prop :=
  ∀ {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes chunk record chunks heap out mark watched : BitVec 64) (value : ValueHOL 64),
    HtrRequestsContext state sha accelerator zeroHashes chunk record chunks heap out →
    ListHashMemoryLayout state sha accelerator zeroHashes chunk heap out watched →
    state.locals.lookup (ofString "mark") = some (.val (.word mark)) →
    watched.toNat < chunks.toNat → cost ≤ state.clock →
    evaluateHOLFiniteState state (htrRequestsAt index) = (some (.returned value),post) →
    post.memory watched = state.memory watched

theorem htrRequests_hash_memory : HtrRequestsSuffixMemory 7 htrRequestsCost7 := by
  intro F state post sha accelerator zeroHashes chunk record chunks heap out mark watched value ctx layout atMark before budget run
  let arguments : List (ExpHOL 64) := [.var .local (ofString "ch"),.const 5,.var .local (ofString "out")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word chunks),.val (.word (5#64)),.val (.word out)] := by
    simp [arguments,evalListHOLExact,evalHOLExact,ctx.atChunks,ctx.atOut]
  rw [source_htrRequests_hash] at run
  obtain ⟨middle,normal,last⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_pcontainer") arguments v) run
  have frame := htrPcontainer_call_normal_memory state middle arguments sha accelerator zeroHashes heap chunks 5 out watched
    layout.toHashMemoryLayout args (by decide) (by change htrPcontainerBodyCost + 2 ≤ state.clock at budget; omega) normal
  have keepMark : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := by
    have kept := evaluate_avoidsLocal_flowing (ofString "mark") (.call (some (none,none)) (ofString "htr_pcontainer") arguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept.trans atMark
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_pcontainer") arguments)
  rw [normal] at metadata
  obtain ⟨released,releaseRun,finishRun⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return middle (ofString "heap_release") [.var .local (ofString "mark")] v) last
  have releasedMemory := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans layout.code) (by simp [evalListHOLExact,evalHOLExact,keepMark]) releaseRun
  obtain ⟨finishedMemory,_,_,_⟩ := return_const_state released post 0 value finishRun
  rw [finishedMemory,releasedMemory]
  exact frame

theorem htrRequests_list_memory_step (index next cost : Nat) (tag size offset : BitVec 64)
    (tagBound : tag.toNat ≤ 4) (offsetBound : offset.toNat ≤ 128) (offsetAligned : offset.toNat % 8 = 0)
    (source : htrRequestsAt index = .seq (.call (some (none,none)) (ofString "htr_request_list")
      (htrRequestsListArguments tag size offset)) (htrRequestsAt next))
    (tail : HtrRequestsSuffixMemory next cost) :
    HtrRequestsSuffixMemory index ((htrRequestListUniformCost + 1) + cost) := by
  intro F state output sha accelerator zeroHashes chunk record chunks heap out mark watched value ctx watchLayout atMark before budget run
  obtain ⟨pointer,count,entry,small⟩ := ctx.decoded tag tagBound
  let arguments := htrRequestsListArguments tag size offset
  have args := htrRequests_list_arguments state record tag pointer count chunks size offset ctx.atRecord ctx.atChunks entry
  have firstBudget : htrRequestListUniformCost + 1 ≤ state.clock := (Nat.le_add_right _ _).trans budget
  have first := runBounded_htrRequestList_call_uniform state none arguments tag pointer count size (chunks + offset) heap args
    ctx.layout.atHeap small ctx.layout.heapFits ctx.layout.code firstBudget
  have natural : (chunks + offset).toNat = chunks.toNat + offset.toNat := by
    apply BitVec.toNat_add_of_lt
    have := ctx.chunksFits
    omega
  have aligned : (chunks + offset).toNat % 8 = 0 := by
    rw [natural,Nat.add_mod,ctx.layout.outAligned,offsetAligned]
  have layout : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap (chunks + offset) record :=
    ⟨⟨ctx.layout.atSha,ctx.layout.atAccel,ctx.layout.atZero,ctx.layout.atHeap,aligned,
      (by rw [natural]; have := ctx.chunksFits; omega),Or.inl (by rw [natural]; have := ctx.recordChunks; omega),
      ctx.layout.heapAligned,ctx.layout.heapFits,ctx.layout.heapBefore,ctx.layout.accelAligned,ctx.layout.accelFits,
      ctx.layout.shaFits,ctx.layout.accelOutside,ctx.layout.shaOutside,ctx.layout.code⟩,
      ctx.layout.atChunk,ctx.layout.chunkAligned,ctx.layout.chunkFits,ctx.layout.chunkOutside⟩
  have naturalWatch : ListHashMemoryLayout state sha accelerator zeroHashes chunk heap (chunks + offset) watched :=
    ⟨⟨watchLayout.atSha,watchLayout.atAccel,watchLayout.atZero,watchLayout.atHeap,aligned,
      (by rw [natural]; have := ctx.chunksFits; omega),Or.inl (by rw [natural]; omega),
      watchLayout.heapAligned,watchLayout.heapFits,watchLayout.heapBefore,watchLayout.accelAligned,watchLayout.accelFits,
      watchLayout.shaFits,watchLayout.accelOutside,watchLayout.shaOutside,watchLayout.code⟩,
      watchLayout.atChunk,watchLayout.chunkAligned,watchLayout.chunkFits,watchLayout.chunkOutside⟩
  rw [source] at run
  obtain ⟨post,normal,last⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "htr_request_list") arguments v) run
  have frame := htrRequestList_call_normal_memory state post arguments sha accelerator zeroHashes chunk tag pointer count size heap
    (chunks + offset) watched naturalWatch args small
    ((Nat.add_le_add_right (htrRequestList_cost_le_uniform count small) 1).trans firstBudget) normal
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_request_list") arguments)
  rw [normal] at metadata
  have postCode := metadata.1
  have spent := first.1
  rw [normal] at spent
  change state.clock ≤ post.clock + (htrRequestListUniformCost + 1) at spent
  have remaining : cost ≤ post.clock := by omega
  change evaluateHOLFiniteState state (.call (some (none,none)) (ofString "htr_request_list") arguments) = (none,post) at normal
  have globals := htrRequestList_call_normal_globals state post arguments tag pointer count size (chunks + offset) heap args ctx.layout.atHeap
    ctx.layout.code normal
  have keep (key : MlS) : post.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_request_list") arguments) rfl state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using kept
  have decoded : HtrRequestsDecoded post record := by
    intro field inside
    obtain ⟨p,n,old,bound⟩ := ctx.decoded field inside
    exact ⟨p,n,htrRequestList_call_normal_decoded_frame state post arguments sha accelerator zeroHashes chunk tag pointer count size heap
      (chunks + offset) record field p n layout args old inside ctx.recordHeap (by rw [natural]; have := ctx.recordChunks; omega)
      ctx.shaRecord ctx.accelRecord ctx.chunkRecord small
      ((Nat.add_le_add_right (htrRequestList_cost_le_uniform count small) 1).trans firstBudget) normal,bound⟩
  have tailFrame := tail post output sha accelerator zeroHashes chunk record chunks heap out mark watched value
    (ctx.after_call keep globals postCode decoded) (watchLayout.transfer globals postCode) ((keep _).trans atMark) before remaining last
  exact tailFrame.trans frame


theorem htrRequests_list4_memory : HtrRequestsSuffixMemory 6 htrRequestsCost6 :=
  htrRequests_list_memory_step 6 7 _ 4 68 128 (by decide) (by decide) (by decide)
    source_htrRequests_list_4 htrRequests_hash_memory

theorem htrRequests_list3_memory : HtrRequestsSuffixMemory 5 htrRequestsCost5 :=
  htrRequests_list_memory_step 5 6 _ 3 184 96 (by decide) (by decide) (by decide)
    source_htrRequests_list_3 htrRequests_list4_memory

theorem htrRequests_list2_memory : HtrRequestsSuffixMemory 4 htrRequestsCost4 :=
  htrRequests_list_memory_step 4 5 _ 2 116 64 (by decide) (by decide) (by decide)
    source_htrRequests_list_2 htrRequests_list3_memory

theorem htrRequests_list1_memory : HtrRequestsSuffixMemory 3 htrRequestsCost3 :=
  htrRequests_list_memory_step 3 4 _ 1 76 32 (by decide) (by decide) (by decide)
    source_htrRequests_list_1 htrRequests_list2_memory

theorem htrRequests_list0_memory : HtrRequestsSuffixMemory 2 htrRequestsCost2 :=
  htrRequests_list_memory_step 2 3 _ 0 192 0 (by decide) (by decide) (by decide)
    source_htrRequests_list_0 htrRequests_list1_memory

#print axioms htrRequests_hash_memory
#print axioms htrRequests_list_memory_step
#print axioms htrRequests_list0_memory
#print axioms htrRequests_list1_memory
#print axioms htrRequests_list2_memory
#print axioms htrRequests_list3_memory
#print axioms htrRequests_list4_memory
end InitECandidate.Runtime
