import InitECandidate.Runtime.DecodeHeaderTimestampFieldReach
import InitECandidate.Runtime.GuardOnlyFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def decodeHeaderTimestampGuard : ProgHOL 64 :=
  .ite (.cmp .lower (.const 8) (.rfield 1 (.var .local (ofString "tsf"))))
    (.raise (ofString "HdrErr") (.const 12)) .skip

theorem source_decode_header_timestamp_guard : decodeHeaderAt 32 =
    .seq decodeHeaderTimestampGuard (decodeHeaderAt 33) := rfl

/-- The actual timestamp width guard either reaches the next word call
unchanged or rejects; neither path consumes source clock. -/
theorem decode_header_timestamp_guard_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) :
    Reaches s (decodeHeaderAt 32) (fun post => post = s) 0 (decodeHeaderAt 33) := by
  rw [source_decode_header_timestamp_guard]
  apply runBounded_seq_reaches s decodeHeaderTimestampGuard (decodeHeaderAt 33) _ 0
    (RunBounded.ofProg (ProgBounded.straight _ rfl) code (by omega))
  · intro value
    exact (evaluate_guard_only_flow decodeHeaderTimestampGuard rfl s).2 value
  · intro post normal
    have same := (evaluate_guard_only_flow decodeHeaderTimestampGuard rfl s).1 (congrArg Prod.fst normal)
    rw [normal] at same
    exact same

#print axioms source_decode_header_timestamp_guard
#print axioms decode_header_timestamp_guard_reaches
end InitECandidate.Runtime
