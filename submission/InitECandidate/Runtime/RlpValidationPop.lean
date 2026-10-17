import InitECandidate.Runtime.RlpValidationFinish
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original stack-pop execution restores all three saved words without
changing memory, globals or clock. Reads refer to the original stack record. -/
theorem evaluate_rlpValidation_pop {F : Type} (state : PanSemStateFiniteExact 64 F)
    (position stop top savedPosition savedStop savedTop : BitVec 64)
    (positionLocal : state.locals.lookup (ofString "pos") = some (.val (.word position)))
    (stopLocal : state.locals.lookup (ofString "end") = some (.val (.word stop)))
    (topLocal : state.locals.lookup (ofString "top") = some (.val (.word top)))
    (readPosition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one (.const (top + 0))) = some (.val (.word savedPosition)))
    (readStop : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one (.const (top + 8))) = some (.val (.word savedStop)))
    (readTop : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.load .one (.const (top + 16))) = some (.val (.word savedTop))) :
    evaluateHOLFiniteState state rlpValidationPop =
      (none,setVarHOLFinite (ofString "top") (.val (.word savedTop))
        (setVarHOLFinite (ofString "end") (.val (.word savedStop))
          (setVarHOLFinite (ofString "pos") (.val (.word savedPosition)) state))) := by
  let first := setVarHOLFinite (ofString "pos") (.val (.word savedPosition)) state
  let second := setVarHOLFinite (ofString "end") (.val (.word savedStop)) first
  have loadFirst : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .local (ofString "top"),.const 0])) = some (.val (.word savedPosition)) := by
    simpa [evalHOLExact,evalListHOLExact,topLocal,wordOpHOL,wordOp,valueIsWord,valueWord] using readPosition
  have loadSecond : @evalHOLExact 64 F _ first.toExact
      (fun address => Classical.propDecidable (first.memaddrs address))
      (.load .one (.op .add [.var .local (ofString "top"),.const 8])) = some (.val (.word savedStop)) := by
    have h : first.locals.lookup (ofString "top") = some (.val (.word top)) := by
      simpa [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "pos" ≠ ofString "top" by decide] using topLocal
    simp only [evalHOLExact,evalListHOLExact,h,wordOpHOL,wordOp] at readStop ⊢
    convert readStop using 1
    simp [first,setVarHOLFinite,valueIsWord,valueWord]
    congr 1
  have loadThird : @evalHOLExact 64 F _ second.toExact
      (fun address => Classical.propDecidable (second.memaddrs address))
      (.load .one (.op .add [.var .local (ofString "top"),.const 16])) = some (.val (.word savedTop)) := by
    have h : second.locals.lookup (ofString "top") = some (.val (.word top)) := by
      simpa [second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "pos" ≠ ofString "top" by decide,show ofString "end" ≠ ofString "top" by decide] using topLocal
    simp only [evalHOLExact,evalListHOLExact,h,wordOpHOL,wordOp] at readTop ⊢
    convert readTop using 1
    simp [second,first,setVarHOLFinite,valueIsWord,valueWord]
    congr 1
  have one : evaluateHOLFiniteState state (.assign .local (ofString "pos")
      (.load .one (.op .add [.var .local (ofString "top"),.const 0]))) = (none,first) := by
    rw [evaluateHOLFiniteState_assign,loadFirst]
    simp [lookupKvarHOLExact,isValidValueHOLExact,
      positionLocal,setKvarHOLFinite,shapeOfHOLExact,shapeEqHOL,first]
  have two : evaluateHOLFiniteState first (.assign .local (ofString "end")
      (.load .one (.op .add [.var .local (ofString "top"),.const 8]))) = (none,second) := by
    rw [evaluateHOLFiniteState_assign,loadSecond]
    simp [lookupKvarHOLExact,isValidValueHOLExact,
      first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,stopLocal,setKvarHOLFinite,
      shapeOfHOLExact,shapeEqHOL,second,show ofString "pos" ≠ ofString "end" by decide]
  have three : evaluateHOLFiniteState second (.assign .local (ofString "top")
      (.load .one (.op .add [.var .local (ofString "top"),.const 16]))) =
      (none,setVarHOLFinite (ofString "top") (.val (.word savedTop)) second) := by
    rw [evaluateHOLFiniteState_assign,loadThird]
    simp [lookupKvarHOLExact,isValidValueHOLExact,
      second,first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,topLocal,setKvarHOLFinite,
      shapeOfHOLExact,shapeEqHOL,show ofString "pos" ≠ ofString "top" by decide,show ofString "end" ≠ ofString "top" by decide]
  rw [source_rlpValidation_pop,evaluateHOLFiniteState_seq_line780,one]
  dsimp only
  rw [evaluateHOLFiniteState_seq_line780,two]
  exact three

theorem rlpValidation_pop_post {F : Type} (state : PanSemStateFiniteExact 64 F)
    (savedPosition savedStop savedTop : BitVec 64) :
    let post := setVarHOLFinite (ofString "top") (.val (.word savedTop))
      (setVarHOLFinite (ofString "end") (.val (.word savedStop))
        (setVarHOLFinite (ofString "pos") (.val (.word savedPosition)) state))
    post.locals.lookup (ofString "pos") = some (.val (.word savedPosition)) ∧
      post.locals.lookup (ofString "end") = some (.val (.word savedStop)) ∧
      post.locals.lookup (ofString "top") = some (.val (.word savedTop)) ∧
      post.clock = state.clock ∧ post.memory = state.memory ∧ post.globals = state.globals := by
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "top" ≠ ofString "pos" by decide,show ofString "end" ≠ ofString "pos" by decide,
    show ofString "top" ≠ ofString "end" by decide]

#print axioms rlpValidation_pop_post
#print axioms evaluate_rlpValidation_pop
end InitECandidate.Runtime
