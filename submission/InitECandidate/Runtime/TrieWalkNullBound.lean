import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def trieWalkLoop : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_trie_walk with
  | .dec _ _ _ (.seq loop _) => loop
  | _ => .skip

def trieWalkStep : ProgHOL 64 :=
  match trieWalkLoop with
  | .while _ body => body
  | _ => .skip

def trieWalkEmptyReturn : ProgHOL 64 := .return (.rstruct [.const 0,.const 0,.const 0])

theorem source_trieWalk_body : sourceFunctionBody Guest.guestFn_trie_walk =
    .dec (ofString "pos") .one (.const 0) (.seq trieWalkLoop trieWalkEmptyReturn) := by
  simp only [trieWalkLoop,trieWalkEmptyReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_trieWalk_loop : trieWalkLoop =
    .while (.cmp .notEqual (.var .local (ofString "node")) (.const 0)) trieWalkStep := by
  simp only [trieWalkLoop,trieWalkStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The original traversal of the empty trie skips its loop even at zero fuel. -/
theorem evaluate_trieWalk_null_loop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node : state.locals.lookup (ofString "node") = some (.val (.word (0 : BitVec 64)))) :
    evaluateHOLFiniteState state trieWalkLoop = (none,state) := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .notEqual (.var .local (ofString "node")) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,node,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_trieWalk_loop,evaluateHOLFiniteState_while_total,evalHOLFinite_eq_toExact,condition]
  rfl

/-- Empty-root traversal has zero body clock cost and cannot time out. No
memory layout or nibble-array validity is needed on this exit path. -/
theorem evaluate_trieWalk_null_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (node : state.locals.lookup (ofString "node") = some (.val (.word (0 : BitVec 64)))) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trie_walk)).2.clock = state.clock ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trie_walk)).1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "pos") (.val (.word (0 : BitVec 64))) state
  have enteredNode : entered.locals.lookup (ofString "node") = some (.val (.word (0 : BitVec 64))) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "pos" ≠ ofString "node" from by decide] using node
  have straight : straightLine trieWalkEmptyReturn = true := rfl
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_trie_walk) =
      (let output := evaluateHOLFiniteState entered trieWalkEmptyReturn;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "pos",state.locals.lookup (ofString "pos"))})) := by
    rw [source_trieWalk_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered (.seq trieWalkLoop trieWalkEmptyReturn); _) = _
    rw [evaluateHOLFiniteState_seq_line780,evaluate_trieWalk_null_loop entered enteredNode]
  rw [full]
  exact ⟨clockPreserving_of_straightLine _ straight entered,
    evaluate_straightLine_no_timeout _ straight entered⟩

#print axioms source_trieWalk_body
#print axioms source_trieWalk_loop
#print axioms evaluate_trieWalk_null_loop
#print axioms evaluate_trieWalk_null_body
end InitECandidate.Runtime
