import InitECandidate.Runtime.SszFixedListCountCallBound
import InitECandidate.Runtime.SszFixedListCountFrame
import InitECandidate.Runtime.PanDecCallContinuationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Compose the actual fixed-list count declaration with any bounded
continuation, retaining its memory and globals on a returned count. -/
theorem evaluate_sszFixedListCount_continuation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (tailCost : Nat) (arguments : List (ExpHOL 64))
    (length size limit : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word length),.val (.word size),.val (.word limit)])
    (code : state.code = originalRuntimeCode) (nonzero : size ≠ 0)
    (budget : 67 + tailCost ≤ state.clock)
    (continuationBound : ∀ (value : ValueHOL 64) (ready : PanSemStateFiniteExact 64 F),
      ready.locals = state.locals.update (name,value) → ready.code = state.code → ready.memaddrs = state.memaddrs →
      ready.memory = state.memory → ready.globals = state.globals → tailCost ≤ ready.clock →
      let evaluated := evaluateHOLFiniteState ready continuation
      ready.clock ≤ evaluated.2.clock + tailCost ∧ evaluated.2.clock ≤ ready.clock ∧ evaluated.1 ≠ some .timeOut) :
    let evaluated := evaluateHOLFiniteState state (.decCall name .one (ofString "ssz_fixed_list_count") arguments continuation)
    state.clock ≤ evaluated.2.clock + (67 + tailCost) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "len",.val (.word length))).update
      (ofString "sz",.val (.word size))).update (ofString "lim",.val (.word limit))
  let entry := callEntryStateHOLFinite state callee
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "sz" ≠ ofString "len" by decide,show ofString "lim" ≠ ofString "len" by decide]
  have atSize : entry.locals.lookup (ofString "sz") = some (.val (.word size)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "lim" ≠ ofString "sz" by decide]
  have atLimit : entry.locals.lookup (ofString "lim") = some (.val (.word limit)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_sszFixedListCount_body entry length size limit code atLength atSize atLimit nonzero
  have lookup := pan_three_word_lookup state.code.lookup (ofString "ssz_fixed_list_count")
    (ofString "len") (ofString "sz") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
    length size limit (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_sszFixedListCount_lookup)
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count)
  have frame := evaluate_sszFixedListCount_body_frame entry length size code atLength atSize nonzero
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) with
  | mk result post =>
    rw [bodyRun] at bounded metadata frame
    dsimp only at bounded metadata frame
    have consumed : state.clock ≤ post.clock + 67 := by
      have spent := bounded.1
      change state.clock - 1 ≤ post.clock + 66 at spent
      omega
    apply evaluate_decCall_continuation_bounded state post name (ofString "ssz_fixed_list_count")
      .one .one arguments [.val (.word length),.val (.word size),.val (.word limit)]
      (sourceFunctionBody Guest.guestFn_ssz_fixed_list_count) continuation callee result
      67 tailCost args lookup (by omega) bodyRun bounded.2.1 consumed
      (bounded.2.2.1 (by change 66 ≤ state.clock - 1; omega))
    intro value returned
    have benign : SszBenign result := Or.inr (Or.inr (Or.inr ⟨value,returned⟩))
    obtain ⟨memory,globals⟩ := frame benign
    let ready := setVarHOLFinite name value {post with locals := state.locals}
    exact continuationBound value ready rfl metadata.1 metadata.2.1 memory globals
      (by change tailCost ≤ post.clock; omega)

#print axioms evaluate_sszFixedListCount_continuation_bounded
end InitECandidate.Runtime
