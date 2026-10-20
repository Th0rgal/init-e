import InitECandidate.Runtime.EvmOperandStackGrowthSource
import InitECandidate.Runtime.EncodeHeaderNormalPlan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A normally completed original growth branch necessarily passed its actual
1024-element limit guard. -/
theorem stack_push_growth_guard_normal {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (capacity : BitVec 64)
 (atCapacity : s.locals.lookup (ofString "cap")=some (.val (.word capacity)))
 (run : evaluateHOLFiniteState s (stackPushGrowthAt 0)=(none,post)) :
 capacity.toNat<1024 ∧evaluateHOLFiniteState s (stackPushGrowthAt 1)=(none,post) := by
 rw [source_stack_push_growth_0] at run
 obtain ⟨middle,guardRun,tailRun⟩:=encode_header_seq_normal s post _ _ run
 have small : capacity.toNat<1024 := by
  by_contra notSmall
  have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
   (.cmp .notLower (.var .local (ofString "cap")) (.const 1024))=some (.val (.word 1)) := by
   simp [evalHOLExact,atCapacity,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,notSmall]
  rw [evaluateHOLFiniteState_ite,cmp] at guardRun
  change evaluateHOLFiniteState s (.raise (ofString "EvmErr") (.const 3))=(none,middle) at guardRun
  simp only [evaluateHOLFiniteState_raise,evalHOLExact] at guardRun
  split at guardRun
  · split at guardRun <;> cases guardRun
  · cases guardRun
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .notLower (.var .local (ofString "cap")) (.const 1024))=some (.val (.word 0)) := by
  simp [evalHOLExact,atCapacity,Flapjack.Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,small]
 rw [evaluateHOLFiniteState_ite,cmp] at guardRun
 change evaluateHOLFiniteState s .skip=(none,middle) at guardRun
 rw [evaluateHOLFiniteState_skip] at guardRun
 have equal : middle=s := (Prod.mk.inj guardRun).2.symm
 subst middle
 exact ⟨small,tailRun⟩
#print axioms stack_push_growth_guard_normal
end InitECandidate.Runtime
