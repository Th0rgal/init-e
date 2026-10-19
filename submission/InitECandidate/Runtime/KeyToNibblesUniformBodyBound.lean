import InitECandidate.Runtime.KeyToNibblesMainUniformBound
import InitECandidate.Runtime.KeyToNibblesTailUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original nibble conversion has an input-linear bound without
source or destination readability premises. Byte errors terminate early. -/
theorem evaluate_keyToNibbles_body_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (small : length.toNat + 4 < 2^64)
    (n : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : length.toNat / 4 + 3 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_key_to_nibbles) = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat / 4 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0#64))) state
  have initial : entered.locals.lookup (ofString "i") = some (.val (.word (0#64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atN : entered.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "n" by decide] using n
  obtain ⟨result,middle,run,cost,remaining,safe,completed,_⟩ := evaluate_keyToNibbles_main_loop_bounded
    entered length small initial atN (by change length.toNat / 4 ≤ state.clock; omega)
  have sequence : ∃ result post, evaluateHOLFiniteState entered
      (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))) = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat / 4 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut := by
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | some stopped => exact ⟨_,_,rfl,by change state.clock ≤ _ at cost; omega,remaining,safe⟩
    | none =>
      obtain ⟨⟨⟨index,atIndex,bounded,aligned⟩,localN⟩,zero⟩ := completed rfl
      have remainder : length.toNat - index.toNat ≤ 3 := by
        have rankEq : keyToNibblesBoundRank middle length = length.toNat / 4 - index.toNat / 4 := by
          simp [keyToNibblesBoundRank,atIndex]
        rw [rankEq] at zero
        omega
      obtain ⟨tailResult,tailPost,tailRun,tailCost,tailRemaining,tailSafe,_,_⟩ :=
        evaluate_keyToNibbles_tail_loop_bounded middle length index bounded small atIndex localN
          (by change state.clock ≤ middle.clock + length.toNat / 4 at cost; omega)
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780,tailRun]
      cases tailResult with
      | some stopped =>
        exact ⟨_,_,rfl,by change state.clock ≤ middle.clock + length.toNat / 4 at cost; omega,
          by change middle.clock ≤ state.clock at remaining; omega,tailSafe⟩
      | none =>
        simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
        exact ⟨_,_,rfl,by change state.clock ≤ middle.clock + length.toNat / 4 at cost; dsimp only [emptyLocalsHOLFinite]; omega,
          by change middle.clock ≤ state.clock at remaining; dsimp only [emptyLocalsHOLFinite]; omega,by simp⟩
  obtain ⟨result,post,sequenceRun,total,remaining,safe⟩ := sequence
  refine ⟨result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))},?_,total,remaining,safe⟩
  rw [source_keyToNibbles_body,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let out := evaluateHOLFiniteState entered (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))); (out.1,{out.2 with locals := HolFiniteMapExact.resVarEq out.2.locals (ofString "i",state.locals.lookup (ofString "i"))})) = _
  rw [sequenceRun]

#print axioms evaluate_keyToNibbles_body_uniform_bounded
end InitECandidate.Runtime
