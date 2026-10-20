import InitECandidate.Runtime.MemoryCostGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- Actual early tuple return or unchanged-state skip continuation. -/
theorem memory_cost_pair_guard_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (word fee expansion : BitVec 64) (name : MlS) (tail : ProgHOL 64) (value : ValueHOL 64)
 (atPair : s.locals.lookup name=some (.rStruct [.val (.word fee),.val (.word expansion)]))
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word word)))
 (run : evaluateHOLFiniteState s (.seq (.ite condition (.return (.var .local name)) .skip) tail)=(some (.returned value),post)) :
 value=.rStruct [.val (.word fee),.val (.word expansion)] ∨
 word=0#64 ∧evaluateHOLFiniteState s tail=(some (.returned value),post) := by
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluated] at run
 by_cases zero : word=0#64
 · right
   refine ⟨zero,?_⟩
   simpa [zero,evaluateHOLFiniteState_skip] using run
 · left
   simpa [zero,evaluateHOLFiniteState_return,evalHOLExact,atPair,shapeOfHOLExact,sizeOfShapeWithContextHOL] using (Prod.mk.inj run).1.symm
/-- The actual early tuple return retains memory and globals. -/
theorem memory_cost_pair_guard_memory_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (word fee expansion : BitVec 64) (name : MlS) (tail : ProgHOL 64) (value : ValueHOL 64)
 (atPair : s.locals.lookup name=some (.rStruct [.val (.word fee),.val (.word expansion)]))
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word word)))
 (run : evaluateHOLFiniteState s (.seq (.ite condition (.return (.var .local name)) .skip) tail)=(some (.returned value),post)) :
 (value=.rStruct [.val (.word fee),.val (.word expansion)] ∧post.memory=s.memory ∧post.globals=s.globals) ∨
 word=0#64 ∧evaluateHOLFiniteState s tail=(some (.returned value),post) := by
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluated] at run
 by_cases zero : word=0#64
 · right
   refine ⟨zero,?_⟩
   simpa [zero,evaluateHOLFiniteState_skip] using run
 · left
   have equality : (some (PanSemResultExact.returned (.rStruct [.val (.word fee),.val (.word expansion)])),emptyLocalsHOLFinite s)=(some (.returned value),post) := by
    simpa [zero,evaluateHOLFiniteState_return,evalHOLExact,atPair,shapeOfHOLExact,sizeOfShapeWithContextHOL] using run
   have returned:=PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj equality).1)
   have postEq:=(Prod.mk.inj equality).2
   exact ⟨returned.symm,by rw [←postEq];rfl,by rw [←postEq];rfl⟩
#print axioms memory_cost_pair_guard_memory_returned

#print axioms memory_cost_pair_guard_returned
end InitECandidate.Runtime
