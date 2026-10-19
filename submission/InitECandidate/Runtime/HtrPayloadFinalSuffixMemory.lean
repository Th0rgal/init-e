import InitECandidate.Runtime.HtrPayloadFinalSuffixBound
import InitECandidate.Runtime.HtrPcontainerMemory
import InitECandidate.Runtime.HashMemoryLayout
import InitECandidate.Runtime.HeapReleaseMemory
import InitECandidate.Runtime.HtrU64AtMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual final payload container hash and outer release preserve a
word outside the SHA workspaces and final output buffer. -/
theorem htrPayload_container_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap chunks out mark watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (budget : htrPayloadContainerSuffixCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 35) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPayload_container] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.var .local (ofString "ch"),.const 19,.var .local (ofString "out")] =
      some [.val (.word chunks),.val (.word (19#64)),.val (.word out)] := by
    simp [evalListHOLExact,evalHOLExact,atChunks,atOut]
  have frame := htrPcontainer_call_normal_memory state middle _ sha accelerator zeroHashes heap chunks 19 out watched layout
    arguments (by decide) (by unfold htrPayloadContainerSuffixCost at budget; omega) normal
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (none,none)) (ofString "htr_pcontainer")
      [.var .local (ofString "ch"),.const 19,.var .local (ofString "out")])
  rw [normal] at metadata
  have keep := evaluate_avoidsLocal_flowing (ofString "mark")
    (.call (some (none,none)) (ofString "htr_pcontainer")
      [.var .local (ofString "ch"),.const 19,.var .local (ofString "out")]) rfl state
    (by rw [normal]; exact Or.inl rfl)
  rw [normal] at keep
  rw [source_htrPayload_finish] at tail
  obtain ⟨released,release,returned⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) middle v) tail
  have keptMark : middle.locals.lookup (ofString "mark") = some (.val (.word mark)) := keep.trans atMark
  have releaseFrame := heapRelease_call_normal_memory middle released (.var .local (ofString "mark")) mark
    (metadata.1.trans layout.code) (by simp [evalListHOLExact,evalHOLExact,keptMark]) release
  have finalFrame := evaluate_readOnly_memory (.return (.const 0)) rfl released
  rw [returned] at finalFrame
  exact (congrFun finalFrame watched).trans ((congrFun releaseFrame watched).trans frame)

/-- The last scalar hash writes inside the 608-byte payload chunk array,
then the actual final container/release suffix keeps the watched word. -/
theorem htrPayload_final_suffix_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (sha accelerator zeroHashes heap raw chunks out mark watched : BitVec 64) (value : ValueHOL 64)
    (layout : HashMemoryLayout state sha accelerator zeroHashes heap out watched)
    (atRaw : state.locals.lookup (ofString "raw") = some (.val (.word raw)))
    (atChunks : state.locals.lookup (ofString "ch") = some (.val (.word chunks)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (atMark : state.locals.lookup (ofString "mark") = some (.val (.word mark)))
    (chunksAligned : chunks.toNat % 8 = 0) (chunksFits : chunks.toNat + 608 ≤ 33806089496)
    (chunksBefore : watched.toNat < chunks.toNat)
    (budget : htrPayloadFinalSuffixCost ≤ state.clock)
    (run : evaluateHOLFiniteState state (htrPayloadAt 34) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [source_htrPayload_last_u64] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_noDirectReturnWhile _ (by decide) state v) run
  let args : List (ExpHOL 64) :=
    [.op .add [.var .local (ofString "raw"),.const 532],
      .op .add [.var .local (ofString "ch"),.const 576]]
  have arguments : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) args =
      some [.val (.word (raw + (532#64))),.val (.word (chunks + (576#64)))] := by
    simp [args,evalListHOLExact,evalHOLExact,atRaw,atChunks,wordOpHOL,wordOp,valueIsWord,valueWord]
  have natural : (chunks + (576#64)).toNat = chunks.toNat + 576 := word_add_toNat chunks 576 (by omega)
  have enough : 30 ≤ state.clock := by
    change 30 + htrPayloadContainerSuffixCost ≤ state.clock at budget
    omega
  have frame := htrU64At_call_normal_memory state middle args (raw + (532#64)) (chunks + (576#64)) watched
    arguments layout.code (by rw [natural,Nat.add_mod,chunksAligned]) (by rw [natural]; omega)
    (Or.inl (by rw [natural]; omega)) enough normal
  have globals := htrU64At_call_globals args state layout.code
  have metadata := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "htr_u64_at") args)
  have bounded := RunBounded.ofProg (ProgBounded.call htrU64At_funBounded (destination := none) args) layout.code enough
  unfold RunBounded at bounded
  rw [normal] at globals metadata bounded
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have kept := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "htr_u64_at") args) rfl state
      (by rw [normal]; exact Or.inl rfl)
    rw [normal] at kept
    exact kept
  have spent : state.clock ≤ middle.clock + 30 := bounded.1
  have remaining : htrPayloadContainerSuffixCost ≤ middle.clock := by
    change 30 + htrPayloadContainerSuffixCost ≤ state.clock at budget
    generalize htrPayloadContainerSuffixCost = cost at budget ⊢
    omega
  have suffix := htrPayload_container_suffix_returned_memory middle post sha accelerator zeroHashes heap chunks out mark watched value
    (layout.transfer globals metadata.1) ((keep _).trans atChunks) ((keep _).trans atOut) ((keep _).trans atMark) remaining tail
  exact suffix.trans frame

#print axioms htrPayload_container_suffix_returned_memory
#print axioms htrPayload_final_suffix_returned_memory
end InitECandidate.Runtime
