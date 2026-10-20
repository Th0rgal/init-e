import InitECandidate.Runtime.PanDomainStores
import InitECandidate.Runtime.PanDomainWhile
import InitECandidate.Runtime.PanDomainCall
import InitECandidate.Runtime.PanDomainDecCall
import InitECandidate.Runtime.PanDomainShared
import InitECandidate.Runtime.PanDomainFfi
import Flapjack.Pancake.Semantics.PanSem.EvaluateInd
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Widening ordinary memory accessibility preserves every non-error actual
source evaluation, including timeout, exceptions, FFI events, and clock. -/
theorem evaluateHOLFiniteState_memaddrs_mono {F : Type} (s : PanSemStateFiniteExact 64 F) (program : ProgHOL 64)
    (domain : BitVec 64→Prop) (subset : ∀address,s.memaddrs address→domain address)
    (nonerror : (evaluateHOLFiniteState s program).1≠some .error) :
    evaluateHOLFiniteState {s with memaddrs:=domain} program=
      ((evaluateHOLFiniteState s program).1,{(evaluateHOLFiniteState s program).2 with memaddrs:=domain}) := by
  have all : ∀ program (state : PanSemStateFiniteExact 64 F),PanDomainMonoAt program state := by
    apply evaluateIndHOL (fun pair : ProgHOL 64×PanSemStateFiniteExact 64 F => PanDomainMonoAt pair.1 pair.2)
    refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · exact panDomainMono_skip
    · exact fun name shape initializer body state ih=>panDomainMono_dec state name shape initializer body ih
    · exact fun kind name expression state=>panDomainMono_assign state kind name expression
    · exact fun name operator expressions state=>panDomainMono_primitive state name operator expressions
    · exact fun destination source state=>panDomainMono_store state destination source
    · exact fun destination source state=>panDomainMono_store32 state destination source
    · exact fun destination source state=>panDomainMono_storeByte state destination source
    · exact fun operator kind name address state=>panDomainMono_shMemLoad state operator kind name address
    · exact fun operator address value state=>panDomainMono_shMemStore state operator address value
    · exact fun first second state ih=>panDomainMono_seq state first second ih.1 ih.2
    · exact fun condition yes no state ih=>panDomainMono_ite state condition yes no ih
    · exact panDomainMono_break
    · exact panDomainMono_continue
    · intro condition body state ih
      rcases ih with ⟨ihContinue,ihNormal,ihBody⟩
      apply panDomainMono_while state condition body
      · intro word conditionRun nonzero clock
        exact ihBody (.val (.word word)) (.word word) word ⟨conditionRun,rfl,rfl,nonzero,clock⟩
      · intro word result post conditionRun nonzero clock run again
        rcases again with normal|continued
        · subst result
          exact ihNormal (.val (.word word)) (.word word) word none post ⟨conditionRun,rfl,rfl,nonzero,clock,run.symm,rfl⟩
        · subst result
          exact ihContinue (.val (.word word)) (.word word) word (some .continue) post .continue ⟨conditionRun,rfl,rfl,nonzero,clock,run.symm,rfl,rfl⟩
    · exact fun expression state=>panDomainMono_return state expression
    · exact fun id expression state=>panDomainMono_raise state id expression
    · exact panDomainMono_tick
    · exact fun a b state=>panDomainMono_annot state a b
    · intro info function arguments state ih
      rcases ih with ⟨ihHandler,ihBody⟩
      apply panDomainMono_call state info function arguments
      · intro args body callee returnShape argsRun lookup clock
        exact ihBody args (body,callee,returnShape) body (callee,returnShape) callee returnShape ⟨argsRun,lookup,rfl,rfl,clock⟩
      · intro args body callee returnShape post exceptionId value destination handlerId handlerVar handlerProgram shape argsRun lookup clock run infoEq same shapeRun valueShape allowed
        exact ihHandler args (body,callee,returnShape) body (callee,returnShape) callee returnShape (some (.exception exceptionId value),post)
          (some (.exception exceptionId value)) post (.exception exceptionId value) exceptionId value (destination,some (handlerId,handlerVar,handlerProgram)) destination
          (some (handlerId,handlerVar,handlerProgram)) (handlerId,handlerVar,handlerProgram) handlerId (handlerVar,handlerProgram) handlerVar handlerProgram shape
          ⟨argsRun,lookup,rfl,rfl,clock,run.symm,rfl,rfl,rfl,infoEq,rfl,rfl,rfl,rfl,same,shapeRun,valueShape,allowed⟩
    · intro name shape function arguments continuation state ih
      rcases ih with ⟨ihContinuation,ihBody⟩
      apply panDomainMono_decCall state name shape function arguments continuation
      · intro args body callee returnShape argsRun lookup clock
        exact ihBody args (body,callee,returnShape) body (callee,returnShape) callee returnShape ⟨argsRun,lookup,rfl,rfl,clock⟩
      · intro args body callee returnShape post value argsRun lookup clock run valueShape returnValueShape
        exact ihContinuation args (body,callee,returnShape) body (callee,returnShape) callee returnShape (some (.returned value),post)
          (some (.returned value)) post (.returned value) value
          ⟨argsRun,lookup,rfl,rfl,clock,run.symm,rfl,rfl,rfl,valueShape,returnValueShape⟩
    · exact fun function a b c d state=>panDomainMono_extCall state function a b c d
  exact all program s domain subset nonerror
#print axioms evaluateHOLFiniteState_memaddrs_mono
end InitECandidate.Runtime
