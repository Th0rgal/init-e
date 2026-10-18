import InitECandidate.Runtime.MerkleizeSource
import InitECandidate.Runtime.PanDecWordResultScope
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed original Merkle level halves the real outer counter;
neither the SHA calls nor the two temporary scopes can hide that update. -/
theorem merkleLevel_body_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (cur : BitVec 64)
    (counter : state.locals.lookup (ofString "cur") = some (.val (.word cur)))
    (run : evaluateHOLFiniteState state merkleLevelBody = (none,post)) :
    post.locals.lookup (ofString "cur") = some (.val (.word (cur >>> 1))) := by
  rw [source_merkleLevel_body] at run
  have initialized : @evalHOLExact 64 F _ state.toExact
      (fun a => Classical.propDecidable (state.memaddrs a))
      (.shift .lsr (.var .local (ofString "cur")) (.const 1)) = some (.val (.word (cur >>> 1))) := by
    simp [evalHOLExact,counter,wordShiftHOL]
  obtain ⟨afterHalf,innerRun,halfScope⟩ := evaluate_dec_word_result_scope state post (ofString "half")
    _ (cur >>> 1) _ none initialized run
  obtain ⟨inner,loopTailRun,indexScope⟩ := evaluate_dec_word_result_scope
    (setVarHOLFinite (ofString "half") (.val (.word (cur >>> 1))) state) afterHalf
    (ofString "j") (.const (0#64)) 0 _ none rfl innerRun
  let entered := setVarHOLFinite (ofString "j") (.val (.word (0#64)))
    (setVarHOLFinite (ofString "half") (.val (.word (cur >>> 1))) state)
  have localHalf : entered.locals.lookup (ofString "half") = some (.val (.word (cur >>> 1))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "j" ≠ ofString "half" by decide]
  change evaluateHOLFiniteState entered
    (.seq merklePairLoop (.assign .local (ofString "cur") (.var .local (ofString "half")))) =
    (none,inner) at loopTailRun
  rw [evaluateHOLFiniteState_seq_line780] at loopTailRun
  cases loopRun : evaluateHOLFiniteState entered merklePairLoop with
  | mk result middle =>
    rw [loopRun] at loopTailRun
    cases result with
    | some result => cases loopTailRun
    | none =>
      have frame := evaluate_avoidsLocal_flowing (ofString "half") merklePairLoop (by decide)
        entered (by rw [loopRun]; exact Or.inl rfl)
      rw [loopRun] at frame
      have atHalf : middle.locals.lookup (ofString "half") = some (.val (.word (cur >>> 1))) := frame.trans localHalf
      have innerCounter : inner.locals.lookup (ofString "cur") = some (.val (.word (cur >>> 1))) := by
        dsimp only at loopTailRun
        rw [evaluateHOLFiniteState_assign] at loopTailRun
        simp only [evalHOLExact,atHalf] at loopTailRun
        split at loopTailRun
        · cases loopTailRun
          simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
        · cases loopTailRun
      have afterHalfCounter : afterHalf.locals.lookup (ofString "cur") = some (.val (.word (cur >>> 1))) := by
        rw [indexScope]
        change (HolFiniteMapExact.resVarEq inner.locals _).lookup _ = _
        rw [resVarEq_lookup,if_neg (show ofString "cur" ≠ ofString "j" by decide)]
        exact innerCounter
      rw [halfScope]
      change (HolFiniteMapExact.resVarEq afterHalf.locals _).lookup _ = _
      rw [resVarEq_lookup,if_neg (show ofString "cur" ≠ ofString "half" by decide)]
      exact afterHalfCounter

#print axioms merkleLevel_body_normal
end InitECandidate.Runtime
