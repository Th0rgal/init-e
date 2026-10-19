import InitECandidate.Runtime.ProgressiveAfterClipMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem progressiveStep_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer accelerator zeroHashes p n off size roots k heap watched : BitVec 64)
    (atPointer : state.globals.lookup (ofString "sha_st") = some (.val (.word pointer)))
    (atAccel : state.globals.lookup (ofString "sha_accel") = some (.val (.word accelerator)))
    (atZero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word zeroHashes)))
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho : state.locals.lookup (ofString "off") = some (.val (.word off)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hs : state.locals.lookup (ofString "size") = some (.val (.word size)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hk : state.locals.lookup (ofString "k") = some (.val (.word k)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (counters : ProgressivePowerCounters n off size k)
    (running : off.toNat < n.toNat)
    (rootsAligned : roots.toNat % 8 = 0) (rootsFits : roots.toNat + 768 ≤ 33806089496)
    (rootsBefore : watched.toNat < roots.toNat)
    (heapAligned : heap.toNat % 8 = 0) (heapFits : heap.toNat ≤ 33806089496) (heapBefore : watched.toNat < heap.toNat)
    (accelAligned : accelerator.toNat % 8 = 0)
    (accelFits : accelerator.toNat + 96 ≤ 33806089496) (pointerFits : pointer.toNat + 64 ≤ 33806089496)
    (accelOutside : watched.toNat < accelerator.toNat ∨ accelerator.toNat + 96 ≤ watched.toNat)
    (pointerOutside : watched.toNat < pointer.toNat ∨ pointer.toNat + 64 ≤ watched.toNat)
    (code : state.code = originalRuntimeCode) (budget : merkleBodyCost + 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state progressiveStep = (none,post)) :
    post.memory watched = state.memory watched := by
  rw [source_progressive_step] at run
  have init : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.op .sub [.var .local (ofString "n"),.var .local (ofString "off")]) =
      some (.val (.word (n - off))) := by
    simp [evalHOLExact,evalListHOLExact,hn,ho,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "cnt") _ (n - off) _ none init run
  rw [evaluateHOLFiniteState_seq_line780,evaluate_progressive_clip state n off size hs] at bodyRun
  dsimp only at bodyRun
  have keep (key : MlS) (different : key ≠ ofString "cnt") :
      (progressiveClippedState state n off size).locals.lookup key = state.locals.lookup key :=
    progressive_clipped_other_local state n off size key different
  have frame := progressiveAfterClip_normal_memory (progressiveClippedState state n off size) inner
    pointer accelerator zeroHashes p off (progressiveChunkCount n off size) size roots k heap watched
    (by unfold progressiveClippedState; split <;> exact atPointer)
    (by unfold progressiveClippedState; split <;> exact atAccel)
    (by unfold progressiveClippedState; split <;> exact atZero)
    ((keep _ (by decide)).trans hp) ((keep _ (by decide)).trans ho) (progressive_clipped_count state n off size)
    ((keep _ (by decide)).trans hs) ((keep _ (by decide)).trans hr) ((keep _ (by decide)).trans hk)
    (by unfold progressiveClippedState; split <;> exact hh)
    ((progressive_chunk_bound n off size (Nat.le_of_lt running)).trans small)
    (progressive_power_root_index n off size k small counters)
    rootsAligned rootsFits rootsBefore heapAligned heapFits heapBefore accelAligned accelFits pointerFits accelOutside pointerOutside
    (by unfold progressiveClippedState; split <;> exact code)
    (by unfold progressiveClippedState; split <;> exact budget) bodyRun
  have memory : (progressiveClippedState state n off size).memory = state.memory := by
    unfold progressiveClippedState; split <;> rfl
  rw [scope]
  exact frame.trans (congrFun memory watched)

#print axioms progressiveStep_normal_memory
end InitECandidate.Runtime
