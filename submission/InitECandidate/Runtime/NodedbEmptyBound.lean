import InitECandidate.Runtime.NodedbBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- A zero-entry database never evaluates a slice load or a hash call. -/
theorem runBounded_nodedb_empty_suffix {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word (0#64)))) :
    RunBounded s (nodedbAt 3) 0 := by
  rw [source_nodedb_insertion]
  apply RunBounded.decConst
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0#64))) s
  have n : entered.locals.lookup (ofString "n") = some (.val (.word (0#64))) := by
    simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTotal
  have idx : entered.locals.lookup (ofString "i") = some (.val (.word (0#64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have zero := eval_nodedb_loop_condition entered 0 0 idx n
  have emptyLoop : evaluateHOLFiniteState entered nodedbInsertionLoop = (none,entered) := by
    apply while_false
    simpa using zero
  have bounded : RunBounded entered (.seq nodedbInsertionLoop (.return (.var .local (ofString "t")))) 0 := by
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780,emptyLoop]
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) code (by omega)
  simpa [entered,setVarHOLFinite] using bounded

/-- Empty decoded witness lists have a bounded original builder even though
their array pointer is zero. Only allocation's actual heap/domain premises are
needed; there are no hash workspace or array-geometry assumptions. -/
theorem runBounded_nodedb_empty_body {F : Type} (s : PanSemStateFiniteExact 64 F) (pointer : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word (0#64))))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (budget : 45 ≤ s.clock) :
    RunBounded s (sourceFunctionBody Guest.guestFn_nodedb_build) 45 := by
  rw [source_nodedb_body,source_nodedb_capacity_declaration]
  apply RunBounded.decConst
  let entered := setVarHOLFinite (ofString "cap") (.val (.word (4#64))) s
  have cap : entered.locals.lookup (ofString "cap") = some (.val (.word (4#64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entered.locals.lookup (ofString "n") = some (.val (.word (0#64))) := by
    simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTotal
  have zero := eval_nodedb_capacity_condition entered 4 0 cap n (by decide)
  have emptyLoop : evaluateHOLFiniteState entered nodedbCapacityLoop = (none,entered) := by
    apply while_false
    simpa using zero
  have ctor : RunBounded entered (nodedbAt 2) 45 := by
    apply runBounded_nodedb_constructor entered pointer 4 2 0 code cap atHeap aligned capped arena (by decide) budget
    intro next ready remaining
    have nextN := (ready.2.1 _ (by decide)).trans n
    exact runBounded_nodedb_empty_suffix next (ready.2.2.1.trans code) nextN
  have bounded : RunBounded entered (nodedbAt 1) 45 := by
    rw [source_nodedb_capacity]
    unfold RunBounded
    rw [evaluateHOLFiniteState_seq_line780,emptyLoop]
    exact ctor
  simpa [entered,setVarHOLFinite] using bounded

#print axioms runBounded_nodedb_empty_suffix
#print axioms runBounded_nodedb_empty_body
end InitECandidate.Runtime
