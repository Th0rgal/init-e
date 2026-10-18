import InitECandidate.Runtime.StatelessInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def inputBlobAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_input_blob
  | n + 1 => statelessNext (inputBlobAt n)
def inputBlobLengthLoad : ProgHOL 64 :=
  .shMemLoad .opW .local (ofString "len") (.const 1073741832)
def inputBlobGuard : ProgHOL 64 :=
  .ite (.cmp .lower (.const 134217712) (.var .local (ofString "len")))
    (.call (some (none,none)) (ofString "trap_with") [.const 8]) .skip
def inputBlobCondition : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "len"))
def inputBlobLoad : ProgHOL 64 :=
  .shMemLoad .opW .local (ofString "w") (.op .add [.const 1073741840,.var .local (ofString "i")])
def inputBlobStep : ProgHOL 64 :=
  .seq inputBlobLoad (.seq (.store (.op .add [.var .local (ofString "p"),.var .local (ofString "i")])
    (.var .local (ofString "w")))
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 8])))
def inputBlobLoop : ProgHOL 64 := .while inputBlobCondition inputBlobStep

theorem source_inputBlob_stages :
    inputBlobAt 0 = .dec (ofString "len") .one (.const 0) (inputBlobAt 1) ∧
    inputBlobAt 1 = .seq inputBlobLengthLoad (inputBlobAt 2) ∧
    inputBlobAt 2 = .seq inputBlobGuard (inputBlobAt 3) ∧
    inputBlobAt 3 = .decCall (ofString "p") .one (ofString "alloc")
      [.op .add [.var .local (ofString "len"),.const 8]] (inputBlobAt 4) ∧
    inputBlobAt 4 = .dec (ofString "i") .one (.const 0) (inputBlobAt 5) ∧
    inputBlobAt 5 = .dec (ofString "w") .one (.const 0) (inputBlobAt 6) ∧
    inputBlobAt 6 = .seq inputBlobLoop (inputBlobAt 7) ∧
    inputBlobAt 7 = .return (.rstruct [.var .local (ofString "p"),.var .local (ofString "len")]) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩ <;>
    simp only [inputBlobAt,statelessNext,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq] <;> rfl

#print axioms source_inputBlob_stages
end InitECandidate.Runtime
