import InitECandidate.Runtime.RawCallOtherLeafBudget
namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall

theorem instruction_zero {width : Nat} [NeZero width] {C F : Type}
    (instruction : Compiler.Encoders.Asm.HolInst width) (info : Spt Nat)
    (source target post : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info (.inst instruction)) info target post result ∧
    BoundedSimulationResult (comp info (.inst instruction)) info target post result := by
  obtain ⟨execution, nonerror, relation⟩ := hypothesis
  rw [StackSemEvaluate.evaluate_inst] at execution
  cases primitive : StackSemInst.instHOL instruction source with
  | none =>
    simp [primitive] at execution
    obtain ⟨rfl, _⟩ := execution
    exact (nonerror rfl).elim
  | some final =>
    simp only [primitive, Prod.mk.injEq] at execution
    obtain ⟨rfl, rfl⟩ := execution
    obtain ⟨targetState, postRelation, targetExecution⟩ :=
      instHOL_stateRel instruction info source target final relation primitive
    apply unchanged_pair (.inst instruction) info target final targetState none rfl rfl postRelation
    simp only [StackSemEvaluate.evaluate_inst, targetExecution]

/-- All nonrecursive RawCall cases; recursive execution sites are excluded. -/
def zeroClockLeaf {width : Nat} [NeZero width] (p : HolProg width) : Bool :=
  match p with
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ | .jumpLower _ _ _ | .rawCall _ | .call _ _ _ => false
  | _ => true

/-- All 28 nonrecursive cases preserve both original simulations with zero extra clock. -/
theorem zeroClockLeaf_correct {width : Nat} [NeZero width] {C F : Type}
    (p : HolProg width) (source target post : StackSemStateFiniteExact width C F)
    (info : Spt Nat) (result : Option (StackSemResult width))
    (leaf : zeroClockLeaf p = true)
    (hypothesis : StackSemEvaluate.evaluate (p, source) = (result, post) ∧
      result ≠ some .error ∧ stateRel info source target) :
    BoundedSimulationResult (compTop info p) info target post result ∧
    BoundedSimulationResult (comp info p) info target post result := by
  cases p with
  | skip  => exact basic_zero _ (.skip ) info source target post result hypothesis
  | halt v => exact basic_zero _ (.halt v) info source target post result hypothesis
  | get v name => exact basic_zero _ (.get v name) info source target post result hypothesis
  | set name v => exact basic_zero _ (.set name v) info source target post result hypothesis
  | opCurrHeap op dest src => exact basic_zero _ (.opCurrHeap op dest src) info source target post result hypothesis
  | tick  => exact basic_zero _ (.tick ) info source target post result hypothesis
  | ret v => exact control_zero _ (.ret v) info source target post result hypothesis
  | raise v => exact control_zero _ (.raise v) info source target post result hypothesis
  | «break» v => exact control_zero _ (.«break» v) info source target post result hypothesis
  | «continue» v => exact control_zero _ (.«continue» v) info source target post result hypothesis
  | stackAlloc n => exact stack_zero _ (.stackAlloc n) info source target post result hypothesis
  | stackFree n => exact stack_zero _ (.stackFree n) info source target post result hypothesis
  | stackLoad a b => exact stack_zero _ (.stackLoad a b) info source target post result hypothesis
  | stackLoadAny a b => exact stack_zero _ (.stackLoadAny a b) info source target post result hypothesis
  | stackStore a b => exact stack_zero _ (.stackStore a b) info source target post result hypothesis
  | stackStoreAny a b => exact stack_zero _ (.stackStoreAny a b) info source target post result hypothesis
  | stackGetSize a => exact stack_zero _ (.stackGetSize a) info source target post result hypothesis
  | stackSetSize a => exact stack_zero _ (.stackSetSize a) info source target post result hypothesis
  | bitmapLoad a b => exact stack_zero _ (.bitmapLoad a b) info source target post result hypothesis
  | codeBufferWrite a b => exact memory_zero _ (.codeBufferWrite a b) info source target post result hypothesis
  | dataBufferWrite a b => exact memory_zero _ (.dataBufferWrite a b) info source target post result hypothesis
  | ffi fi a b c d e => exact memory_zero _ (.ffi fi a b c d e) info source target post result hypothesis
  | shMemOp op reg addr =>
      cases addr with
      | addr address offset =>
          exact memory_zero _ (.shMemOp op reg address offset) info source target post result hypothesis
  | inst instruction => exact instruction_zero instruction info source target post result hypothesis
  | locValue a b c => exact compCorrectLocValue a b c info source target post result hypothesis
  | alloc reg => exact compCorrectAlloc reg info source target post result hypothesis
  | storeConsts a b stub => exact compCorrectStoreConsts a b stub info source target post result hypothesis
  | install a b c d e => exact compCorrectInstall a b c d e info source target post result hypothesis
  | seq _ _ | ite _ _ _ _ _ | loop _ | jumpLower _ _ _ | rawCall _ | call _ _ _ =>
      simp [zeroClockLeaf] at leaf

#print axioms zeroClockLeaf_correct
end InitECandidate.Runtime.StackRawCall
