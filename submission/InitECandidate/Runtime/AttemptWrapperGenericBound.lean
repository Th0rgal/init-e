import InitECandidate.Runtime.AttemptWrapperSource
import InitECandidate.Runtime.RunBoundedHandledCall
import InitECandidate.Runtime.PanSingleWordLookup
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Actual one-parameter callee map of every attempt wrapper and run_attempt. -/
def attemptSiCallee (si : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  HolFiniteMapExact.empty.update (ofString "si",.val (.word si))
/-- The exact run-entry context after depth calls. Only locals and clock change. -/
def attemptEntry {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (depth : Nat) :
    PanSemStateFiniteExact 64 F := {s with locals:=attemptSiCallee si,clock:=s.clock-depth}
theorem attemptEntry_context {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (depth : Nat) :
    (attemptEntry s si depth).memory=s.memory ∧ (attemptEntry s si depth).globals=s.globals ∧
    (attemptEntry s si depth).memaddrs=s.memaddrs ∧ (attemptEntry s si depth).code=s.code ∧
    (attemptEntry s si depth).be=s.be := ⟨rfl,rfl,rfl,rfl,rfl⟩
theorem attemptEntry_nested {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (a b : Nat) :
    attemptEntry (attemptEntry s si a) si b=attemptEntry s si (a+b) := by
  simp only [attemptEntry,Nat.sub_sub]
theorem attemptEntry_si {F : Type} (s : PanSemStateFiniteExact 64 F) (si : BitVec 64) (depth : Nat) :
    (attemptEntry s si depth).locals.lookup (ofString "si")=some (.val (.word si)) := by
  simp [attemptEntry,attemptSiCallee,HolFiniteMapExact.lookup_update,FUPDATE]
theorem attempt_reject_handler_bounded (tag : BitVec 64) : ProgBounded (attemptRejectHandler tag) 0 := by
  have shared : ProgBounded (.shMemStore .op8 (.op .add [.const 2688614400#64,.const 70#64])
      (.var .local (ofString "e"))) 0 := by
    intro F state _ _
    have clock:=evaluate_shared_store_clock state .op8 (.op .add [.const 2688614400#64,.const 70#64])
      (.var .local (ofString "e"))
    exact ⟨by omega,by omega,evaluate_shared_store_no_timeout state _ _ _⟩
  have raised : ProgBounded (.raise (ofString "Fail") (.const tag)) 0 := ProgBounded.straight _ rfl
  intro F state code budget
  exact ProgBounded.seq shared raised state code budget
theorem verify_attempt_handler_bounded : ProgBounded verifyAttemptHandler 0 := ProgBounded.straight _ rfl
/-- Generic actual handled call followed by a return. Handler is clock-free;
all body, shape failure, exception and FFI outcomes are included. -/
theorem runBounded_attempt_call_return {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si : BitVec 64) (function exceptionId : MlS) (body handler : ProgHOL 64) (returnExpr : ExpHOL 64)
    (cost : Nat) (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (installed : originalRuntimeCode.lookup function=some ([(ofString "si",.one)],body,.one))
    (code : s.code=originalRuntimeCode) (budget : cost+1≤s.clock)
    (bounded : RunBounded (attemptEntry s si 1) body cost) (handlerBound : ProgBounded handler 0) :
    RunBounded s (.seq (.call (some (none,some (exceptionId,ofString "e",handler))) function
      [.var .local (ofString "si")]) (.return returnExpr)) (cost+1) := by
  have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a))
      [.var .local (ofString "si")]=some [.val (.word si)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atSi]
  have lookup := pan_single_word_lookup s.code.lookup function (ofString "si") body si (by rw [code];exact installed)
  have inner : RunBounded (callEntryStateHOLFinite s (attemptSiCallee si)) body cost := bounded
  have called := RunBounded.handledCall s function exceptionId (ofString "e") none _ _ body handler
    (attemptSiCallee si) .one cost 0 args lookup code (by omega) inner handlerBound
  have whole := RunBounded.seq (tail:=.return returnExpr) (b:=0) called (by omega) (by
    intro next normal nextCode ticks
    exact RunBounded.ofProg (ProgBounded.straight _ rfl) (nextCode.trans code) (Nat.zero_le _))
  simpa only [Nat.add_zero] using whole
/-- An original rejection layer has one call tick; its declaration and shared
output-byte handler contribute no source clock ticks. -/
theorem runBounded_attempt_layer {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si : BitVec 64) (function exceptionId : MlS) (tag : BitVec 64) (body : ProgHOL 64) (cost : Nat)
    (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
    (installed : originalRuntimeCode.lookup function=some ([(ofString "si",.one)],body,.one))
    (code : s.code=originalRuntimeCode) (budget : cost+1≤s.clock)
    (bounded : RunBounded (attemptEntry s si 1) body cost) :
    RunBounded s (attemptLayerBody function exceptionId tag) (cost+1) := by
  unfold attemptLayerBody
  apply RunBounded.decConst s (ofString "e") (0#64)
  let entered:=setVarHOLFinite (ofString "e") (.val (.word (0#64))) s
  apply runBounded_attempt_call_return entered si function exceptionId body (attemptRejectHandler tag) (.const 0#64) cost
  · simpa (config := {decide := true}) [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atSi
  · exact installed
  · exact code
  · exact budget
  · simpa only [entered,attemptEntry,setVarHOLFinite] using bounded
  · exact attempt_reject_handler_bounded tag
#print axioms runBounded_attempt_layer
#print axioms attemptEntry_context
end InitECandidate.Runtime
