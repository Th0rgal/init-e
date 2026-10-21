import InitECandidate.Runtime.StackExecutionNativeLeaves
import InitECandidate.Runtime.StackExecutionNativeCalls
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- The three compiler conclusions have distinct control/terminal protocols. -/
inductive ExecutionKind where
  | normal
  | exit (result : StackSemResult 64)
  | terminal (result : StackSemResult 64) (outcome : HolOutcome)

def ExecutionKind.result : ExecutionKind → Option (StackSemResult 64)
  | .normal => none
  | .exit result | .terminal result _ => some result

abbrev ExecutionLocalPrice (F : Type) :=
  HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat

/-- Uniform recursive compiler motive, with cost supplied by the independent
executed-cost definition. This definition contains no trace or native oracle. -/
def ExecutionKindBound {F : Type} (price : ExecutionLocalPrice F) (p : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) : ExecutionKind → Prop
  | .normal => NormalWeightedFlatten p source (executionCostPrice price p source)
  | .exit result => ExitWeightedFlatten p source result (executionCostPrice price p source)
  | .terminal result outcome => TerminalWeightedFlatten p source result outcome (executionCostPrice price p source)

/-- Explicit local encoding-price inequalities. These are obligations to
instantiate for the concrete compiled artifact, not assumed execution bounds. -/
structure LocalNativeCaps {F : Type} (price : ExecutionLocalPrice F) : Prop where
  instruction : ∀ source instruction encoded pc,
    LabToTarget.LocalCost.instructionWork encoded pc instruction ≤ price (.inst instruction) source encoded
  location : ∀ source reg sid lid encoded pc,
    LabToTarget.controlWork 2 encoded pc ≤ price (.locValue reg sid lid) source encoded
  tick : ∀ source encoded pc,
    LabToTarget.LocalCost.instructionWork encoded pc .skip ≤ price .tick source encoded
  breakPrice : ∀ source index encoded, 2 ≤ price (.break index) source encoded
  returnPrice : ∀ source reg encoded, 1 ≤ price (.ret reg) source encoded
  raisePrice : ∀ source reg encoded, 1 ≤ price (.raise reg) source encoded
  ffi : ∀ source name ptr len ptr2 len2 ret encoded pc,
    LabToTarget.controlWork 2 encoded pc + 17 ≤ price (.ffi name ptr len ptr2 len2 ret) source encoded
  shared : ∀ source op reg base offset encoded,
    1 ≤ price (.shMemOp op reg (.addr base offset)) source encoded
  branch : ∀ source cmp reg operand yes no encoded pc,
    LabToTarget.controlWork 3 encoded pc + 2 ≤ price (.ite cmp reg operand yes no) source encoded
  loopPrice : ∀ source body encoded, 2 ≤ price (.loop body) source encoded
  tailCall : ∀ source dest encoded, callJumpWork dest ≤ price (.call none dest none) source encoded
  rawCall : ∀ source dest encoded, 2 ≤ price (.rawCall dest) source encoded
  returnCall : ∀ source rp link l1 l2 dest handler encoded pc,
    LabToTarget.controlWork 2 encoded pc + callJumpWork dest + 2 ≤
      price (.call (some (rp, link, l1, l2)) dest handler) source encoded
  jumpLower : ∀ source regX regY dest encoded pc,
    LabToTarget.controlWork 3 encoded pc ≤ price (.jumpLower regX regY dest) source encoded

/-- Eligible post-removal leaves and their semantic result class. Return and
raise retain actual source register reads and installed-location validity. -/
inductive ExecutionLeaf {F : Type} (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    HolProg 64 → ExecutionKind → Prop where
  | skip : ExecutionLeaf source .skip .normal
  | inst (instruction : HolInst 64) : ExecutionLeaf source (.inst instruction) .normal
  | location (reg sid lid : Nat) : ExecutionLeaf source (.locValue reg sid lid) .normal
  | tick : ExecutionLeaf source .tick .normal
  | halt (reg : Nat) (value : BitVec 64) (read : StackSemStateOps.getVar reg source = some (.word value)) :
      ExecutionLeaf source (.halt reg) (.terminal (.halt (.word value))
        (if value = 0 then .success else .resourceLimitHit))
  | breakCase (index : Nat) : ExecutionLeaf source (.break index) (.exit (.break index))
  | continueCase (index : Nat) : ExecutionLeaf source (.continue index) (.exit (.continue index))
  | returnCase (reg sid lid : Nat) (read : StackSemStateOps.getVar reg source = some (.loc sid lid))
      (valid : StackSem.locCheckExact source.code (sid, lid)) :
      ExecutionLeaf source (.ret reg) (.exit (.result (.loc sid lid)))
  | raiseCase (reg sid lid : Nat) (read : StackSemStateOps.getVar reg source = some (.loc sid lid))
      (valid : StackSem.locCheckExact source.code (sid, lid)) :
      ExecutionLeaf source (.raise reg) (.exit (.exception (.loc sid lid)))
  | ffiNormal (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) :
      ExecutionLeaf source (.ffi name ptr len ptr2 len2 ret) .normal
  | ffiFinal (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (event : HolFinalEvent) :
      ExecutionLeaf source (.ffi name ptr len ptr2 len2 ret) (.terminal (.finalFFI event) (.ffiOutcome event))
  | sharedNormal (op : HolMemop) (reg base : Nat) (offset : BitVec 64) :
      ExecutionLeaf source (.shMemOp op reg (.addr base offset)) .normal
  | sharedFinal (op : HolMemop) (reg base : Nat) (offset : BitVec 64) (event : HolFinalEvent) :
      ExecutionLeaf source (.shMemOp op reg (.addr base offset)) (.terminal (.finalFFI event) (.ffiOutcome event))

/-- All eligible leaves satisfy the unified compiler motive from local prices.
No constructor of ExecutionLeaf assumes a compiled trace or native bound. -/
theorem ExecutionLeaf.bound {F : Type} {price : ExecutionLocalPrice F}
    (caps : LocalNativeCaps price) {source : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {p : HolProg 64} {kind : ExecutionKind} (leaf : ExecutionLeaf source p kind) :
    ExecutionKindBound price p source kind := by
  cases leaf with
  | skip => exact normalExecutionCost_skip price source
  | inst instruction => exact normalExecutionCost_inst price source instruction (caps.instruction source instruction)
  | location reg sid lid => exact normalExecutionCost_locValue price source reg sid lid (caps.location source reg sid lid)
  | tick => exact normalExecutionCost_tick price source (caps.tick source)
  | halt reg value read => exact terminalExecutionCost_halt price source reg value read
  | breakCase index => exact exitExecutionCost_break price source index (fun encoded _ => caps.breakPrice source index encoded)
  | continueCase index => exact exitExecutionCost_continue price source index
  | returnCase reg sid lid read valid => exact exitExecutionCost_return price source reg sid lid read valid (caps.returnPrice source reg)
  | raiseCase reg sid lid read valid => exact exitExecutionCost_raise price source reg sid lid read valid (caps.raisePrice source reg)
  | ffiNormal name ptr len ptr2 len2 ret =>
    exact normalExecutionCost_ffi price source name ptr len ptr2 len2 ret
      (caps.ffi source name ptr len ptr2 len2 ret)
  | ffiFinal name ptr len ptr2 len2 ret event =>
    apply terminalExecutionCost_ffi price source name ptr len ptr2 len2 ret event
    intro encoded pc
    have h := caps.ffi source name ptr len ptr2 len2 ret encoded pc
    omega
  | sharedNormal op reg base offset =>
    exact normalExecutionCost_shared price source op reg base offset
      (fun encoded _ => caps.shared source op reg base offset encoded)
  | sharedFinal op reg base offset event => exact terminalExecutionCost_shared price source op reg base offset event

#print axioms ExecutionLeaf.bound
end InitECandidate.Runtime.StackToLab
