import InitECandidate.Runtime.StackExecutionTrace
import InitECandidate.Runtime.StackExecutionNativeSeq
import InitECandidate.Runtime.StackExecutionNativeLoop
import InitECandidate.Runtime.StackExecutionNativeConditional
import InitECandidate.Runtime.StackExecutionNativeReturn
import InitECandidate.Runtime.StackExecutionNativePropagate
import InitECandidate.Runtime.StackExecutionNativeJump
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- The recursive native compiler bound for every eligible semantic derivation.
Its cost is the independent executed Stack cost. Only local encoding prices
are assumed; no constructor assumes a native trace or whole-run cost bound.
Trace completeness and concrete price instantiation remain separate tasks. -/
theorem ExecutionTrace.bound {F : Type} {price : ExecutionLocalPrice F}
    (caps : LocalNativeCaps price) {source post : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {p : HolProg 64} {kind : ExecutionKind} (trace : ExecutionTrace source p kind post) :
    ExecutionKindBound price p source kind := by
  induction trace with
  | @leaf source post p kind run classification =>
    exact classification.bound caps
  | @seqNext source middle post first second kind run firstTree secondTree ihFirst ihSecond =>
    cases kind with
    | normal =>
      exact normalExecutionCost_seq_next price first second source middle firstTree.sound ihFirst ihSecond
    | exit result =>
      exact exitExecutionCost_seq_next price first second source middle result firstTree.sound ihFirst ihSecond
    | terminal result outcome =>
      exact terminalExecutionCost_seq_next price first second source middle result outcome firstTree.sound ihFirst ihSecond
  | @seqStop source post first second kind run nonNormal firstTree ihFirst =>
    cases kind with
    | normal =>
      exact False.elim (nonNormal rfl)
    | exit result =>
      exact exitExecutionCost_seq_stop price first second source post result firstTree.sound ihFirst
    | terminal result outcome =>
      exact terminalExecutionCost_seq_stop price first second source post result outcome firstTree.sound ihFirst
  | @branch source post yes no cmp reg operand kind x y choice run lhs rhs chosen selectedTree ih =>
    cases kind with
    | normal =>
      exact normalExecutionCost_if price yes no cmp reg operand source x y choice lhs rhs chosen
        (congrArg Prod.fst selectedTree.sound) (caps.branch source cmp reg operand yes no) ih
    | exit result =>
      exact exitExecutionCost_if price yes no cmp reg operand source x y choice result lhs rhs chosen
        (congrArg Prod.fst selectedTree.sound) (caps.branch source cmp reg operand yes no) ih
    | terminal result outcome =>
      exact terminalExecutionCost_if price yes no cmp reg operand source x y choice result outcome lhs rhs chosen
        (congrArg Prod.fst selectedTree.sound) (caps.branch source cmp reg operand yes no) ih
  | @loopBreak source post body run bodyTree ih =>
    exact normalExecutionCost_loop_break price body source post bodyTree.sound ih
  | @loopStep source middle post body kind run bodyTree clock restTree ihBody ihRest =>
    cases kind with
    | normal =>
      exact normalExecutionCost_loop_step price body source middle bodyTree.sound clock
        (caps.loopPrice source body) ihBody ihRest
    | exit result =>
      exact exitExecutionCost_loop_step price body source middle result bodyTree.sound clock
        (caps.loopPrice source body) ihBody ihRest
    | terminal result outcome =>
      exact terminalExecutionCost_loop_step price body source middle result outcome bodyTree.sound clock
        (caps.loopPrice source body) ihBody ihRest
  | @loopContinue source middle post body kind run bodyTree clock restTree ihBody ihRest =>
    cases kind with
    | normal =>
      exact normalExecutionCost_loop_continue price body source middle bodyTree.sound clock
        (caps.loopPrice source body) ihBody ihRest
    | exit result =>
      exact exitExecutionCost_loop_continue price body source middle result bodyTree.sound clock
        (caps.loopPrice source body) ihBody ihRest
    | terminal result outcome =>
      exact terminalExecutionCost_loop_continue price body source middle result outcome bodyTree.sound clock
        (caps.loopPrice source body) ihBody ihRest
  | @loopExit source post body bodyResult result run bodyTree stopped exited ih =>
    exact exitExecutionCost_loop_exit price body source post bodyResult result bodyTree.sound stopped exited ih
  | @loopFinal source post body bodyResult result outcome run bodyTree stopped exited ih =>
    exact terminalExecutionCost_loop_exit price body source post bodyResult result outcome bodyTree.sound stopped exited ih
  | @callTail source post dest prog kind run positive found nonNormal bodyTree ih =>
    cases kind with
    | normal =>
      exact False.elim (nonNormal rfl)
    | exit result =>
      exact exitExecutionCost_call_tail price source dest prog result positive found (caps.tailCall source dest) ih
    | terminal result outcome =>
      exact terminalExecutionCost_call_tail price source dest prog result outcome positive found (caps.tailCall source dest) ih
  | @rawCall source post dest prologue prog kind run positive found nonNormal bodyTree ih =>
    cases kind with
    | normal =>
      exact False.elim (nonNormal rfl)
    | exit result =>
      exact exitExecutionCost_call_raw price source dest prologue prog result positive found (caps.rawCall source dest) ih
    | terminal result outcome =>
      exact terminalExecutionCost_call_raw price source dest prologue prog result outcome positive found (caps.rawCall source dest) ih
  | @jumpFalse source post regX regY dest x y run readX readY chosen =>
    exact normalExecutionCost_jumpLower_fallthrough price source regX regY dest x y readX readY chosen
      (caps.jumpLower source regX regY dest)
  | @jumpTrue source post regX regY dest prog kind x y run positive readX readY chosen found nonNormal bodyTree ih =>
    have localPrice : ∀ encoded, 3 ≤ price (.jumpLower regX regY dest) source encoded := by
      intro encoded
      have h := caps.jumpLower source regX regY dest encoded 0
      unfold LabToTarget.controlWork at h
      omega
    cases kind with
    | normal =>
      exact False.elim (nonNormal rfl)
    | exit result =>
      exact exitExecutionCost_jumpLower_taken price source regX regY dest x y prog result
        positive readX readY chosen found localPrice ih
    | terminal result outcome =>
      exact terminalExecutionCost_jumpLower_taken price source regX regY dest x y prog result outcome
        positive readX readY chosen found localPrice ih
  | @callReturn source middle post rp prog link l1 l2 dest handler kind run positive found bodyTree returnTree ihBody ihReturn =>
    cases kind with
    | normal =>
      exact normalExecutionCost_call_return price source middle rp prog link l1 l2 dest handler
        positive found bodyTree.sound (caps.returnCall source rp link l1 l2 dest handler) ihBody ihReturn
    | exit result =>
      exact exitExecutionCost_call_return price source middle rp prog link l1 l2 dest handler result
        positive found bodyTree.sound (caps.returnCall source rp link l1 l2 dest handler) ihBody ihReturn
    | terminal result outcome =>
      exact terminalExecutionCost_call_return price source middle rp prog link l1 l2 dest handler result outcome
        positive found bodyTree.sound (caps.returnCall source rp link l1 l2 dest handler) ihBody ihReturn
  | @callHandler source middle post rp hp prog link l1 l2 hs hl dest kind run positive found bodyTree handlerTree ihBody ihHandler =>
    cases kind with
    | normal =>
      exact normalExecutionCost_call_handler price source middle rp prog link l1 l2 dest hp hs hl
        positive found bodyTree.sound (caps.returnCall source rp link l1 l2 dest (some (hp, hs, hl))) ihBody ihHandler
    | exit result =>
      exact exitExecutionCost_call_handler price source middle rp prog link l1 l2 dest hp hs hl result
        positive found bodyTree.sound (caps.returnCall source rp link l1 l2 dest (some (hp, hs, hl))) ihBody ihHandler
    | terminal result outcome =>
      exact terminalExecutionCost_call_handler price source middle rp prog link l1 l2 dest hp hs hl result outcome
        positive found bodyTree.sound (caps.returnCall source rp link l1 l2 dest (some (hp, hs, hl))) ihBody ihHandler
  | @callExit source post rp prog link l1 l2 dest handler result run positive found propagates bodyTree ih =>
    apply exitExecutionCost_call_propagate price source post rp prog link l1 l2 dest handler result
      positive found bodyTree.sound propagates ?_ ih
    intro encoded pc
    have h := caps.returnCall source rp link l1 l2 dest handler encoded pc
    omega
  | @callFinal source post rp prog link l1 l2 dest handler result outcome run positive found propagates bodyTree ih =>
    apply terminalExecutionCost_call_propagate price source post rp prog link l1 l2 dest handler result outcome
      positive found bodyTree.sound propagates ?_ ih
    intro encoded pc
    have h := caps.returnCall source rp link l1 l2 dest handler encoded pc
    omega

#print axioms ExecutionTrace.bound
end InitECandidate.Runtime.StackToLab
