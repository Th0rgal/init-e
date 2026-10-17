import InitECandidate.Runtime.RlpItemBytePaths
import InitECandidate.Runtime.RlpErrorCheck
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpItemShortString : ProgHOL 64 :=
  match rlpItemAfterSingleByte with
  | .seq (.ite _ body _) _ => body
  | _ => .skip

def rlpItemShortBody : ProgHOL 64 :=
  match rlpItemShortString with
  | .dec _ _ _ body => body
  | _ => .skip

def rlpItemShortCanonical : ProgHOL 64 :=
  match rlpItemShortBody with
  | .seq _ (.seq body _) => body
  | _ => .skip

theorem source_rlpItem_short_canonical : rlpItemShortCanonical =
    .ite (.cmp .equal (.var .local (ofString "n")) (.const 1))
      (.ite (.cmp .lower (.loadByte (.op .add [.var .local (ofString "p"),.const 1])) (.const 128))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 4]) .skip) .skip := by
  simp only [rlpItemShortCanonical,rlpItemShortBody,rlpItemShortString,rlpItemAfterSingleByte,
    rlpItemAfterByte,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original one-byte canonicality rule has a one-tick error budget,
including unreadable payloads; passing it leaves the entire state unchanged. -/
theorem evaluate_rlpItem_short_canonical {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpItemShortCanonical = (result,post) ∧
      state.clock ≤ post.clock + 1 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → post = state) ∧ (∀ value, result ≠ some (.returned value)) ∧
      post.memory = state.memory ∧ post.globals = state.globals := by
  rw [source_rlpItem_short_canonical,evaluateHOLFiniteState_ite]
  by_cases one : length = BitVec.ofNat 64 1
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "n")) (.const 1)) = some (.val (.word 1)) := by
      simp [evalHOLExact,lengthLocal,one,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
    exact evaluate_rlp_error_check state
      (.cmp .lower (.loadByte (.op .add [.var .local (ofString "p"),.const 1])) (.const 128)) 4 code ticks
  · have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .equal (.var .local (ofString "n")) (.const 1)) = some (.val (.word 0)) := by
      simp [evalHOLExact,lengthLocal,one,Compiler.Encoders.Asm.wordCmpHOL]
    rw [guard]
    simp only [if_true,evaluateHOLFiniteState_skip]
    exact ⟨none,state,rfl,by omega,by omega,by simp,by simp,by intro value; simp,rfl,rfl⟩

#print axioms evaluate_rlpItem_short_canonical
end InitECandidate.Runtime
