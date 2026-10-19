import InitECandidate.Runtime.HtrRequestListLoopBound
import InitECandidate.Runtime.HtrPlistChunksCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrRequestListLoopCost (count : BitVec 64) : Nat := count.toNat * (htrRequestStepCost + 1)
def htrRequestListSuffixCost (count : BitVec 64) : Nat := htrRequestListLoopCost count + (htrPlistChunksCost + 2)

theorem runBounded_htrRequestList_hash {F : Type} (state : PanSemStateFiniteExact 64 F)
    (roots count out heap : BitVec 64)
    (atRoots : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (atCount : state.locals.lookup (ofString "n") = some (.val (.word count)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : count.toNat ≤ 134217712) (cap : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : htrPlistChunksCost + 2 ≤ state.clock) :
    RunBounded state (htrRequestListAt 4) (htrPlistChunksCost + 2) := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "roots"),.var .local (ofString "n"),
    .var .local (ofString "n"),.var .local (ofString "out")]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word roots),.val (.word count),.val (.word count),.val (.word out)] := by
    simp [arguments,evalListHOLExact,evalHOLExact,atRoots,atCount,atOut]
  rw [source_htrRequestList_hash]
  have first := runBounded_htrPlistChunks_call state none arguments roots count count out heap args small hh cap code (by omega)
  have combined := RunBounded.seq (tail := .seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (.return (.const 0))) (b := 1) first (by omega) (by
    intro post normal postCode remaining
    exact RunBounded.ofProg
      (ProgBounded.seq (ProgBounded.call vmBound_heap_release _ _) (ProgBounded.straight _ (by decide)))
      (postCode.trans code) remaining)
  exact combined

theorem runBounded_htrRequestList_suffix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (kind pointer size roots heap count out : BitVec 64)
    (small : count.toNat ≤ 134217712) (cap : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode)
    (valid : HtrRequestListState kind pointer size roots heap count state count.toNat)
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (budget : htrRequestListSuffixCost count ≤ state.clock) :
    RunBounded state (htrRequestListAt 3) (htrRequestListSuffixCost count) := by
  have loop := htrRequestList_loop_ranked kind pointer size roots heap count small cap count.toNat state code valid
    (by change count.toNat * (htrRequestStepCost + 1) + (htrPlistChunksCost + 2) ≤ state.clock at budget; omega)
  rw [source_htrRequestList_loop]
  exact RunBounded.seq ⟨loop.1,loop.2.1,loop.2.2.1⟩ budget (by
    intro next normal nextCode remaining
    have nextLoop := loop
    rw [normal] at nextLoop
    obtain ⟨_,nextValid,_,_⟩ := nextLoop.2.2.2 rfl
    have keep : next.locals.lookup (ofString "out") = state.locals.lookup (ofString "out") := by
      have frame := evaluate_avoidsLocal_flowing (ofString "out") (.while htrRequestListCondition htrRequestListStep)
        (by decide) state (by rw [normal]; exact Or.inl rfl)
      simpa only [normal] using frame
    exact runBounded_htrRequestList_hash next roots count out heap nextValid.rootsLocal nextValid.countLocal
      (keep.trans atOut) nextValid.heapGlobal small cap (nextCode.trans code) remaining)

#print axioms runBounded_htrRequestList_hash
#print axioms runBounded_htrRequestList_suffix
end InitECandidate.Runtime
