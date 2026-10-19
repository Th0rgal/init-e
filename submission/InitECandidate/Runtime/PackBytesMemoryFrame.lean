import InitECandidate.Runtime.PackBytesBodyBound
import InitECandidate.Runtime.PackBytesMemoryReturned
import InitECandidate.Runtime.PackBytesCopyMemory
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem packBytes_body_returned_memory_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (p n heap watched : BitVec 64) (value : ValueHOL 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (small : n.toNat ≤ 134217712) (aligned : heap.toNat % 8 = 0)
    (before : watched.toNat < heap.toNat)
    (budget : merkleMemoryCallCost + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_pack_bytes) = (some (.returned value),post)) :
    post.memory watched = state.memory watched := by
  rw [sourceFunctionBody_eq_structural] at run
  change evaluateHOLFiniteState state (packBytesAt 0) = _ at run
  rw [source_packBytes_count] at run
  have init : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift .lsr (.op .add [.var .local (ofString "n"),.const 31]) (.const 5)) =
      some (.val (.word (packBytesCount n))) := by
    simp [packBytesCount,evalHOLExact,evalListHOLExact,hn,wordOpHOL,wordOp,valueIsWord,valueWord,wordShiftHOL]
  obtain ⟨inner,bodyRun,scope⟩ := evaluate_dec_word_result_scope state post (ofString "count") _
    (packBytesCount n) _ (some (.returned value)) init run
  let entered := setVarHOLFinite (ofString "count") (.val (.word (packBytesCount n))) state
  have countLocal : entered.locals.lookup (ofString "count") = some (.val (.word (packBytesCount n))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a))
      [.panop .mul [.var .local (ofString "count"),.const 32]] =
      some [.val (.word (packBytesCount n * (32#64)))] := by
    simp [evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  have reached := evaluate_allocation_declaration_reaches entered
    (.panop .mul [.var .local (ofString "count"),.const 32]) (ofString "buf") heap
    (packBytesCount n * (32#64)) (packBytesAt 2) args (by exact code) (by exact hh) heapBound (by change 2 ≤ state.clock; omega)
  rw [← source_packBytes_alloc] at reached
  obtain ⟨ready,allocated,spent,_,agreement,returned⟩ := reaches_returned_continuation entered
    (packBytesAt 1) (packBytesAt 2) _ 2 value reached (by rw [bodyRun])
  have atBuf : ready.locals.lookup (ofString "buf") = some (.val (.word heap)) := by
    rw [allocated.1]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have atCount : ready.locals.lookup (ofString "count") = some (.val (.word (packBytesCount n))) := by
    rw [allocated.1]; simpa (config := {decide := true}) [HolFiniteMapExact.lookup_update,FUPDATE] using countLocal
  have suffixRun : evaluateHOLFiniteState ready (packBytesAt 2) =
      (some (.returned value),(evaluateHOLFiniteState ready (packBytesAt 2)).2) := Prod.ext returned rfl
  have atP : ready.locals.lookup (ofString "p") = some (.val (.word p)) := by
    rw [allocated.1]
    simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using hp
  have atN : ready.locals.lookup (ofString "n") = some (.val (.word n)) := by
    rw [allocated.1]
    simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using hn
  have fits : heap.toNat + (packBytesCount n * (32#64)).toNat ≤ 33806089496 := by
    have cap := allocated.2.2.2.2.2.1
    have covers := allocated.2.2.2.2.2.2.1
    omega
  have suffix := packBytes_memory_returned_frame ready _ heap p n watched value atBuf atP atN atCount
    small aligned fits (Or.inl before) (allocated.2.2.1.trans code)
    (by change state.clock ≤ ready.clock + 2 at spent; omega) suffixRun
  have preserved : inner.memory watched = entered.memory watched := by
    rw [bodyRun] at agreement
    exact (congrFun agreement.2.2.1 watched).trans (suffix.trans (congrFun allocated.2.1 watched))
  rw [scope]
  exact preserved

#print axioms packBytes_body_returned_memory_frame
end InitECandidate.Runtime
