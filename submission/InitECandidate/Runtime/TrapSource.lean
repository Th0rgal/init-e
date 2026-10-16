import InitECandidate.Runtime.AllocationSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def trapDiagnosticAddress (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.const 2688614400,.const offset]

def trapSourceBody : ProgHOL 64 :=
  .seq (.shMemStore .op8 (trapDiagnosticAddress 33) (.var .local (ofString "code")))
    (.seq (.shMemStore .opW (trapDiagnosticAddress 40) (.var .global (ofString "heap_ptr")))
      (.seq (.shMemStore .opW (trapDiagnosticAddress 48) (.var .global (ofString "journal_n")))
        (.seq (.extCall (ofString "trap") .baseAddr (.var .local (ofString "code")) .baseAddr (.const 0))
          (.raise (ofString "TrapErr") (.var .local (ofString "code"))))))

/-- Exact original trap body, including diagnostics before its external call. -/
theorem source_trap_body : sourceFunctionBody Guest.guestFn_trap_with = trapSourceBody := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

/-- Diagnostic writes target the fixed output region. -/
theorem eval_trapDiagnosticAddress {F : Type} (state : PanSemStateFiniteExact 64 F) (offset : BitVec 64) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (trapDiagnosticAddress offset) =
      some (.val (.word (2688614400 + offset))) := by
  simp [trapDiagnosticAddress,evalHOLExact,evalListHOLExact,wordOpHOL,wordOp,valueIsWord,valueWord]

#print axioms source_trap_body
#print axioms eval_trapDiagnosticAddress
end InitECandidate.Runtime
