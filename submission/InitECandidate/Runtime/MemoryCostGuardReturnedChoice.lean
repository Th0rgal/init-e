import InitECandidate.Runtime.MemoryCostGuard
import InitECandidate.Runtime.MemoryCostPureDeclaration
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Exact early-return/skip split for the source cost helper guards. -/
theorem memory_cost_guard_returned_choice {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (condition : ExpHOL 64) (word fee : BitVec 64) (tail : ProgHOL 64) (value : ValueHOL 64)
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) condition=some (.val (.word word)))
 (run : evaluateHOLFiniteState s (.seq (.ite condition (.return (.rstruct [.const fee,.const 0])) .skip) tail)=(some (.returned value),post)) :
 (word≠0#64 ∧value=.rStruct [.val (.word fee),.val (.word (0#64))]) ∨
 word=0#64 ∧evaluateHOLFiniteState s tail=(some (.returned value),post) := by
 rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,evaluated] at run
 by_cases zero : word=0#64
 · right
   refine ⟨zero,?_⟩
   simpa [zero,evaluateHOLFiniteState_skip] using run
 · left
   refine ⟨zero,?_⟩
   have result := (Prod.mk.inj run).1.symm
   simpa [zero,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,shapeOfHOLExact,sizeOfShapeWithContextHOL] using result
#print axioms memory_cost_guard_returned_choice
end InitECandidate.Runtime
