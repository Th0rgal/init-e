import InitECandidate.Runtime.StateStorageInnerSelection
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keccakMainLoop : ProgHOL 64 :=
  match stateInitSpineDrop 3 (sourceFunctionBody Guest.guestFn_keccak256) with
  | .seq loop _ => loop
  | _ => .skip

def keccakMainLoopBody : ProgHOL 64 :=
  match keccakMainLoop with
  | .while _ body => body
  | _ => .skip

def keccakRemainderScope : ProgHOL 64 := stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_keccak256)
def keccakRemainderTail : ProgHOL 64 := stateInitSpineDrop 5 (sourceFunctionBody Guest.guestFn_keccak256)

theorem source_keccak_main_loop : keccakMainLoop =
    .while (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 136])) keccakMainLoopBody := by
  simp only [keccakMainLoopBody,keccakMainLoop,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_keccak_remainder_scope : keccakRemainderScope =
    .dec (ofString "rem") .one (.op .sub [.var .local (ofString "n"),.var .local (ofString "i")]) keccakRemainderTail := by
  simp only [keccakRemainderScope,keccakRemainderTail,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_keccak_after_state_zero : stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_keccak256) =
    .dec (ofString "i") .one (.const 0) (.seq keccakMainLoop keccakRemainderScope) := by
  simp only [keccakMainLoop,keccakRemainderScope,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Short inputs, including the20-byte account address, skip the original
full-block absorption loop without consuming a source tick. -/
theorem evaluate_keccak_short_main_loop {F : Type} (state : PanSemStateFiniteExact 64 F) (size : BitVec 64)
    (n : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (small : size.toNat < 136) :
    evaluateHOLFiniteState state keccakMainLoop = (none,state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 136])) =
      some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,evalListHOLExact,n,i,wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL]
    exact BitVec.lt_def.mpr small
  rw [source_keccak_main_loop,evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
  rfl

/-- After the skipped loop the original remainder declaration binds exactly
n and restores its temporary local around the unchanged source continuation. -/
theorem evaluate_keccak_short_remainder {F : Type} (state : PanSemStateFiniteExact 64 F) (size : BitVec 64)
    (n : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (i : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (small : size.toNat < 136) :
    evaluateHOLFiniteState state (.seq keccakMainLoop keccakRemainderScope) =
      (let output := evaluateHOLFiniteState (setVarHOLFinite (ofString "rem") (.val (.word size)) state) keccakRemainderTail;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "rem",state.locals.lookup (ofString "rem"))})) := by
  rw [evaluateHOLFiniteState_seq_line780,evaluate_keccak_short_main_loop state size n i small]
  change evaluateHOLFiniteState state keccakRemainderScope = _
  rw [source_keccak_remainder_scope,evaluateHOLFiniteState_dec_total]
  simp [evalHOLExact,evalListHOLExact,n,i,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,shapeEqHOL]

#print axioms source_keccak_main_loop
#print axioms source_keccak_remainder_scope
#print axioms source_keccak_after_state_zero
#print axioms evaluate_keccak_short_main_loop
#print axioms evaluate_keccak_short_remainder
end InitECandidate.Runtime
