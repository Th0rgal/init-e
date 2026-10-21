import InitECandidate.Runtime.StackExecutionNativeKernel
import InitECandidate.Runtime.StackWeightedCallPropagate
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Encoders.Asm

/-- A finite semantic execution derivation for the post-removal compiler
fragment. Each node records the actual evaluator equation; child nodes expose
only reached bodies. No constructor contains a native trace, price, or budget.
The evaluator equations make this representation independently checkable;
completeness for the compiled guest remains a separate obligation. -/
inductive ExecutionTrace {F : Type} :
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) → HolProg 64 →
    ExecutionKind → StackSemStateFiniteExact 64 LabToTarget.Config F → Prop where
  | leaf {source post p kind}
      (run : StackSemEvaluate.evaluate (p, source) = (kind.result, post))
      (classification : ExecutionLeaf source p kind) : ExecutionTrace source p kind post
  | seqNext {source middle post first second kind}
      (run : StackSemEvaluate.evaluate (.seq first second, source) = (kind.result, post))
      (firstTrace : ExecutionTrace source first .normal middle)
      (secondTrace : ExecutionTrace middle second kind post) :
      ExecutionTrace source (.seq first second) kind post
  | seqStop {source post first second kind}
      (run : StackSemEvaluate.evaluate (.seq first second, source) = (kind.result, post))
      (nonNormal : kind ≠ .normal)
      (firstTrace : ExecutionTrace source first kind post) :
      ExecutionTrace source (.seq first second) kind post
  | branch {source post yes no cmp reg operand kind} (x y : WordLocW 64) (choice : Bool)
      (run : StackSemEvaluate.evaluate (.ite cmp reg operand yes no, source) = (kind.result, post))
      (lhs : StackSemStateOps.getVar reg source = some x)
      (rhs : StackSemStateOps.getVarImm (HolRegImm.toWordRegImm operand) source = some y)
      (chosen : wordSemWordCmp cmp x y = some choice)
      (selectedTrace : ExecutionTrace source (if choice then yes else no) kind post) :
      ExecutionTrace source (.ite cmp reg operand yes no) kind post
  | loopBreak {source post body}
      (run : StackSemEvaluate.evaluate (.loop body, source) = (none, post))
      (bodyTrace : ExecutionTrace source body (.exit (.break 0)) post) :
      ExecutionTrace source (.loop body) .normal post
  | loopStep {source middle post body kind}
      (run : StackSemEvaluate.evaluate (.loop body, source) = (kind.result, post))
      (bodyTrace : ExecutionTrace source body .normal middle) (clock : middle.clock ≠ 0)
      (restTrace : ExecutionTrace (StackSemStateOps.decClock middle) (.loop body) kind post) :
      ExecutionTrace source (.loop body) kind post
  | loopContinue {source middle post body kind}
      (run : StackSemEvaluate.evaluate (.loop body, source) = (kind.result, post))
      (bodyTrace : ExecutionTrace source body (.exit (.continue 0)) middle) (clock : middle.clock ≠ 0)
      (restTrace : ExecutionTrace (StackSemStateOps.decClock middle) (.loop body) kind post) :
      ExecutionTrace source (.loop body) kind post
  | loopExit {source post body bodyResult result}
      (run : StackSemEvaluate.evaluate (.loop body, source) = (some result, post))
      (bodyTrace : ExecutionTrace source body (.exit bodyResult) post)
      (stopped : StackSemControl.contLoop (some bodyResult) = false)
      (exited : StackSemControl.exitLoop (some bodyResult) = some result) :
      ExecutionTrace source (.loop body) (.exit result) post
  | loopFinal {source post body bodyResult result outcome}
      (run : StackSemEvaluate.evaluate (.loop body, source) = (some result, post))
      (bodyTrace : ExecutionTrace source body (.terminal bodyResult outcome) post)
      (stopped : StackSemControl.contLoop (some bodyResult) = false)
      (exited : StackSemControl.exitLoop (some bodyResult) = some result) :
      ExecutionTrace source (.loop body) (.terminal result outcome) post
  | callTail {source post dest prog kind}
      (run : StackSemEvaluate.evaluate (.call none dest none, source) = (kind.result, post))
      (positive : source.clock ≠ 0)
      (found : StackSemControl.findCode dest source.regs source.code = some prog)
      (nonNormal : kind ≠ .normal)
      (bodyTrace : ExecutionTrace (StackSemStateOps.decClock source) prog kind post) :
      ExecutionTrace source (.call none dest none) kind post
  | rawCall {source post dest prologue prog kind}
      (run : StackSemEvaluate.evaluate (.rawCall dest, source) = (kind.result, post))
      (positive : source.clock ≠ 0) (found : sptLookup dest source.code = some (.seq prologue prog))
      (nonNormal : kind ≠ .normal)
      (bodyTrace : ExecutionTrace (StackSemStateOps.decClock source) prog kind post) :
      ExecutionTrace source (.rawCall dest) kind post
  | jumpFalse {source post regX regY dest} (x y : BitVec 64)
      (run : StackSemEvaluate.evaluate (.jumpLower regX regY dest, source) = (none, post))
      (readX : StackSemStateOps.getVar regX source = some (.word x))
      (readY : StackSemStateOps.getVar regY source = some (.word y))
      (chosen : wordCmpHOL .lower x y = false) :
      ExecutionTrace source (.jumpLower regX regY dest) .normal post
  | jumpTrue {source post regX regY dest prog kind} (x y : BitVec 64)
      (run : StackSemEvaluate.evaluate (.jumpLower regX regY dest, source) = (kind.result, post))
      (positive : source.clock ≠ 0)
      (readX : StackSemStateOps.getVar regX source = some (.word x))
      (readY : StackSemStateOps.getVar regY source = some (.word y))
      (chosen : wordCmpHOL .lower x y = true) (found : sptLookup dest source.code = some prog)
      (nonNormal : kind ≠ .normal)
      (bodyTrace : ExecutionTrace (StackSemStateOps.decClock source) prog kind post) :
      ExecutionTrace source (.jumpLower regX regY dest) kind post
  | callReturn {source middle post rp prog link l1 l2 dest handler kind}
      (run : StackSemEvaluate.evaluate (.call (some (rp, link, l1, l2)) dest handler, source) = (kind.result, post))
      (positive : source.clock ≠ 0)
      (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
      (bodyTrace : ExecutionTrace (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))
        prog (.exit (.result (.loc l1 l2))) middle)
      (returnTrace : ExecutionTrace middle rp kind post) :
      ExecutionTrace source (.call (some (rp, link, l1, l2)) dest handler) kind post
  | callHandler {source middle post rp hp prog link l1 l2 hs hl dest kind}
      (run : StackSemEvaluate.evaluate (.call (some (rp, link, l1, l2)) dest (some (hp, hs, hl)), source) = (kind.result, post))
      (positive : source.clock ≠ 0)
      (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
      (bodyTrace : ExecutionTrace (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))
        prog (.exit (.exception (.loc hs hl))) middle)
      (handlerTrace : ExecutionTrace middle hp kind post) :
      ExecutionTrace source (.call (some (rp, link, l1, l2)) dest (some (hp, hs, hl))) kind post
  | callExit {source post rp prog link l1 l2 dest handler result}
      (run : StackSemEvaluate.evaluate (.call (some (rp, link, l1, l2)) dest handler, source) = (some result, post))
      (positive : source.clock ≠ 0)
      (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
      (propagates : callResultPropagates result handler)
      (bodyTrace : ExecutionTrace (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))
        prog (.exit result) post) :
      ExecutionTrace source (.call (some (rp, link, l1, l2)) dest handler) (.exit result) post
  | callFinal {source post rp prog link l1 l2 dest handler result outcome}
      (run : StackSemEvaluate.evaluate (.call (some (rp, link, l1, l2)) dest handler, source) = (some result, post))
      (positive : source.clock ≠ 0)
      (found : StackSemControl.findCode dest (source.regs.eraseEq link) source.code = some prog)
      (propagates : callResultPropagates result handler)
      (bodyTrace : ExecutionTrace (StackSemStateOps.decClock (StackSemStateOps.setVar link (.loc l1 l2) source))
        prog (.terminal result outcome) post) :
      ExecutionTrace source (.call (some (rp, link, l1, l2)) dest handler) (.terminal result outcome) post

/-- Every derivation is tied to the actual evaluator, including its exact
result and successor state. This does not assert trace completeness. -/
theorem ExecutionTrace.sound {F : Type} {source post : StackSemStateFiniteExact 64 LabToTarget.Config F}
    {p : HolProg 64} {kind : ExecutionKind} (trace : ExecutionTrace source p kind post) :
    StackSemEvaluate.evaluate (p, source) = (kind.result, post) := by
  cases trace <;> assumption

#print axioms ExecutionTrace.sound
end InitECandidate.Runtime.StackToLab
