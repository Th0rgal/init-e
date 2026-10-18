import InitECandidate.Runtime.ProgressiveLoopsBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem source_progressive_counters : progressiveAt 3 =
    .dec (ofString "k") .one (.const 0)
      (.dec (ofString "off") .one (.const 0)
        (.dec (ofString "size") .one (.const 1) (progressiveAt 6))) := by rfl

theorem runBounded_progressive_counters {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n roots heap : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (hr : state.locals.lookup (ofString "roots") = some (.val (.word roots)))
    (hh : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (small : n.toNat ≤ 134217712) (heapBound : heap.toNat ≤ 33806089496)
    (code : state.code = originalRuntimeCode) (budget : progressiveLoopsCost ≤ state.clock) :
    RunBounded state (progressiveAt 3) progressiveLoopsCost := by
  rw [source_progressive_counters]
  apply RunBounded.decConst
  apply RunBounded.decConst
  apply RunBounded.decConst
  apply runBounded_progressive_loops
    (setVarHOLFinite (ofString "size") (.val (.word (1#64)))
      (setVarHOLFinite (ofString "off") (.val (.word (0#64)))
        (setVarHOLFinite (ofString "k") (.val (.word (0#64))) state))) p n roots heap small heapBound (by exact code)
  · apply progressive_initial_rank
    all_goals simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,hp,hn,hr,hh]
  · exact budget

#print axioms source_progressive_counters
#print axioms runBounded_progressive_counters
end InitECandidate.Runtime
