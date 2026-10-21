import InitECandidate.Runtime.StackExecutionNativeBasis
import InitECandidate.Runtime.StackWeightedFfi
import InitECandidate.Runtime.StackWeightedShared
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- The executed local price pays the actual locValue native prefix. -/
theorem normalExecutionCost_locValue {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (reg sid lid : Nat)
    (localPrice : ∀ encoded (pc : Nat), LabToTarget.controlWork 2 encoded pc ≤ price (.locValue reg sid lid) source encoded) :
    NormalWeightedFlatten (.locValue reg sid lid) source (executionCostPrice price (.locValue reg sid lid) source) := by
  apply (normalWeightedFlatten_locValue source reg sid lid).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded pc

/-- The executed local price pays the actual tick native prefix. -/
theorem normalExecutionCost_tick {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (localPrice : ∀ encoded (pc : Nat), LabToTarget.LocalCost.instructionWork encoded pc .skip ≤ price .tick source encoded) :
    NormalWeightedFlatten .tick source (executionCostPrice price .tick source) := by
  apply (normalWeightedFlatten_tick source).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded pc

/-- The executed local price pays the actual break native prefix. -/
theorem exitExecutionCost_break {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (index : Nat)
    (localPrice : ∀ encoded (pc : Nat), 2 ≤ price (.break index) source encoded) :
    ExitWeightedFlatten (.break index) source (.break index) (executionCostPrice price (.break index) source) := by
  apply (exitWeightedFlatten_break source index).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded pc

/-- The executed local price pays the actual continue native prefix. -/
theorem exitExecutionCost_continue {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (index : Nat)
    :
    ExitWeightedFlatten (.continue index) source (.continue index) (executionCostPrice price (.continue index) source) := by
  apply (exitWeightedFlatten_continue source index).mono
  intro encoded pc
  exact Nat.zero_le _

/-- The executed local price pays the actual ffi native prefix. -/
theorem normalExecutionCost_ffi {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat)
    (localPrice : ∀ encoded (pc : Nat), LabToTarget.controlWork 2 encoded pc + 17 ≤ price (.ffi name ptr len ptr2 len2 ret) source encoded) :
    NormalWeightedFlatten (.ffi name ptr len ptr2 len2 ret) source (executionCostPrice price (.ffi name ptr len ptr2 len2 ret) source) := by
  apply (normalWeightedFlatten_ffi source name ptr len ptr2 len2 ret).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded pc

/-- The executed local price pays the actual ffi native prefix. -/
theorem terminalExecutionCost_ffi {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (name : Basis.Pure.MlString.MlString) (ptr len ptr2 len2 ret : Nat) (event : HolFinalEvent)
    (localPrice : ∀ encoded (pc : Nat), LabToTarget.controlWork 2 encoded pc ≤ price (.ffi name ptr len ptr2 len2 ret) source encoded) :
    TerminalWeightedFlatten (.ffi name ptr len ptr2 len2 ret) source (.finalFFI event) (.ffiOutcome event) (executionCostPrice price (.ffi name ptr len ptr2 len2 ret) source) := by
  apply (terminalWeightedFlatten_ffi source name ptr len ptr2 len2 ret event).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded pc

/-- The executed local price pays the actual shared native prefix. -/
theorem normalExecutionCost_shared {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (op : HolMemop) (reg base : Nat) (offset : BitVec 64)
    (localPrice : ∀ encoded (pc : Nat), 1 ≤ price (.shMemOp op reg (.addr base offset)) source encoded) :
    NormalWeightedFlatten (.shMemOp op reg (.addr base offset)) source (executionCostPrice price (.shMemOp op reg (.addr base offset)) source) := by
  apply (normalWeightedFlatten_shared source op reg base offset).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded pc

/-- The executed local price pays the actual shared native prefix. -/
theorem terminalExecutionCost_shared {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (op : HolMemop) (reg base : Nat) (offset : BitVec 64) (event : HolFinalEvent)
    :
    TerminalWeightedFlatten (.shMemOp op reg (.addr base offset)) source (.finalFFI event) (.ffiOutcome event) (executionCostPrice price (.shMemOp op reg (.addr base offset)) source) := by
  apply (terminalWeightedFlatten_shared source op reg base offset event).mono
  intro encoded pc
  exact Nat.zero_le _

/-- The actual installed return location retains its semantic validity premise. -/
theorem exitExecutionCost_return {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (reg sid lid : Nat)
    (read : StackSemStateOps.getVar reg source = some (.loc sid lid))
    (valid : StackSem.locCheckExact source.code (sid, lid))
    (localPrice : ∀ encoded, 1 ≤ price (.ret reg) source encoded) :
    ExitWeightedFlatten (.ret reg) source (.result (.loc sid lid))
      (executionCostPrice price (.ret reg) source) := by
  apply (exitWeightedFlatten_return source reg sid lid read valid).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded

/-- The actual installed raise location retains its semantic validity premise. -/
theorem exitExecutionCost_raise {F : Type}
    (price : HolProg 64 → StackSemStateFiniteExact 64 LabToTarget.Config F → LabProgHOL 64 → Nat)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (reg sid lid : Nat)
    (read : StackSemStateOps.getVar reg source = some (.loc sid lid))
    (valid : StackSem.locCheckExact source.code (sid, lid))
    (localPrice : ∀ encoded, 1 ≤ price (.raise reg) source encoded) :
    ExitWeightedFlatten (.raise reg) source (.exception (.loc sid lid))
      (executionCostPrice price (.raise reg) source) := by
  apply (exitWeightedFlatten_raise source reg sid lid read valid).mono
  intro encoded pc
  simpa only [executionCostPrice, stackExecutionCost] using localPrice encoded

#print axioms normalExecutionCost_locValue
#print axioms normalExecutionCost_tick
#print axioms exitExecutionCost_break
#print axioms exitExecutionCost_continue
#print axioms normalExecutionCost_ffi
#print axioms terminalExecutionCost_ffi
#print axioms normalExecutionCost_shared
#print axioms terminalExecutionCost_shared
#print axioms exitExecutionCost_return
#print axioms exitExecutionCost_raise
end InitECandidate.Runtime.StackToLab
