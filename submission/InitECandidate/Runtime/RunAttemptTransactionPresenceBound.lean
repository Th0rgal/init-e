import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.VariableCountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual transaction-presence loop body after state initialization. -/
def runAttemptTxPresenceBody : ProgHOL 64 :=
 match runAttemptAt 16 with
 | .seq (.while _ body) _ => body
 | _ => .skip
def runAttemptTxPresenceGuard : ProgHOL 64 :=
 match runAttemptTxPresenceBody with
 | .seq guard _ => guard
 | _ => .skip
def runAttemptTxPresenceLoop : ProgHOL 64 :=
 .while (.cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))) runAttemptTxPresenceBody

theorem source_run_attempt_tx_presence_loop : runAttemptAt 16=
 .seq runAttemptTxPresenceLoop (runAttemptAt 17) := by rfl

theorem source_run_attempt_tx_presence_body : runAttemptTxPresenceBody=
 .seq runAttemptTxPresenceGuard
  (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by rfl

/-- A successful guard advances the actual index once; failed reads or empty
transactions terminate immediately. No array readability or reserve is assumed. -/
theorem run_attempt_tx_presence_counted : CountedBody (ofString "i") 1 runAttemptTxPresenceBody 0 := by
 rw [source_run_attempt_tx_presence_body]
 exact CountedBody.seq (a:=0) (b:=0) _ (ProgBounded.straight _ rfl) rfl rfl CountedBody.incr

/-- The original signed loop is bounded for every64-bit declared count.
Negative signed limits skip it; positive limits cannot wrap the zero-start index. -/
theorem runBounded_run_attempt_tx_presence {F : Type} (s : PanSemStateFiniteExact 64 F)
 (count : BitVec 64) (code : s.code=originalRuntimeCode)
 (atIndex : s.locals.lookup (ofString "i")=some (.val (.word (0#64))))
 (atCount : s.locals.lookup (ofString "ntx")=some (.val (.word count)))
 (budget : 2^64-1≤s.clock) : RunBounded s runAttemptTxPresenceLoop (2^64-1) := by
 exact variableCountedWhile_zero_bounded (ofString "i") (ofString "ntx") .less (Or.inl rfl)
  run_attempt_tx_presence_counted (by rfl) s code count atIndex atCount (by simpa using budget)
#print axioms source_run_attempt_tx_presence_loop
#print axioms source_run_attempt_tx_presence_body
#print axioms run_attempt_tx_presence_counted
#print axioms runBounded_run_attempt_tx_presence
end InitECandidate.Runtime
