import InitECandidate.Runtime.KeyToNibblesGeneralMainLoop
import InitECandidate.Runtime.KeyToNibblesGeneralTailLoop
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original conversion establishes a nibble range using at most
length/4 + 3 source clock ticks, including both loops and local scopes. -/
theorem evaluate_keyToNibbles_general_body_range {F : Type} (state : PanSemStateFiniteExact 64 F)
    (key out length : BitVec 64)
    (lengthBound : 2 * length.toNat + 8 < 2^64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (outLocal : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (sourceDomain : ∀ offset : Nat, offset < length.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * length.toNat → state.memaddrs (panByteAlignHOL (out + BitVec.ofNat 64 offset)))
    (n : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (ticks : length.toNat / 4 + 3 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_key_to_nibbles) = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat / 4 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TrieNibbleRange post out (2 * length)) := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  have initial : entered.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atN : entered.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "n" from by decide] using n
  have enteredKey : entered.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "key" by decide] using keyLocal
  have enteredOut : entered.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "i" ≠ ofString "out" by decide] using outLocal
  obtain ⟨result,middle,run,cost,remaining,noTimeout,rangeDone,noReturn⟩ :=
    evaluate_keyToNibbles_general_main_loop_range entered key out length lengthBound enteredKey enteredOut
      sourceDomain outputDomain initial atN (by change length.toNat / 4 ≤ state.clock; omega)
  have sequence : ∃ result post, evaluateHOLFiniteState entered
      (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))) = (result,post) ∧
      state.clock ≤ post.clock + (length.toNat / 4 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TrieNibbleRange post out (2 * length)) := by
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      obtain ⟨index,atIndex,bounded,remainder,valid,keyNow,outNow,nNow,domainNow⟩ := rangeDone rfl
      obtain ⟨tailResult,tailPost,tailRun,tailCost,tailRemaining,tailNoTimeout,tailDone,tailNoReturn⟩ :=
        evaluate_keyToNibbles_general_tail_loop_range middle key out length index lengthBound keyNow outNow
          (by simpa only [domainNow,entered,setVarHOLFinite] using sourceDomain) (by simpa only [domainNow,entered,setVarHOLFinite] using outputDomain)
          atIndex bounded valid nNow (by have entryClock : entered.clock = state.clock := rfl; omega)
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780,tailRun]
      cases tailResult with
      | none =>
        obtain ⟨last,lastLocal,_,equal,finalRange,_⟩ := tailDone rfl
        subst last
        simp only [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
        refine ⟨_,_,rfl,by have entryClock : entered.clock = state.clock := rfl; dsimp only [emptyLocalsHOLFinite]; omega,
          by have entryClock : entered.clock = state.clock := rfl; dsimp only [emptyLocalsHOLFinite]; omega,by simp,?_⟩
        intro value _
        exact finalRange.after_frame rfl rfl rfl
      | some stopped =>
        refine ⟨_,_,rfl,by have entryClock : entered.clock = state.clock := rfl; omega,
          by have entryClock : entered.clock = state.clock := rfl; omega,tailNoTimeout,?_⟩
        intro value returned
        exact False.elim (tailNoReturn value returned)
    | some result =>
      refine ⟨_,_,rfl,by have entryClock : entered.clock = state.clock := rfl; omega,remaining,noTimeout,?_⟩
      intro value returned
      exact False.elim (noReturn value returned)
  obtain ⟨result,post,sequenceRun,total,remaining,noTimeout,range⟩ := sequence
  have full : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_key_to_nibbles) =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "i",state.locals.lookup (ofString "i"))}) := by
    rw [source_keyToNibbles_body,evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    change (let output := evaluateHOLFiniteState entered (.seq keyToNibblesMainLoop (.seq keyToNibblesTailLoop (.return (.const 0)))); _) = _
    rw [sequenceRun]
  refine ⟨result,_,full,total,remaining,noTimeout,?_⟩
  intro value returned
  exact (range value returned).after_frame rfl rfl rfl

#print axioms evaluate_keyToNibbles_general_body_range
end InitECandidate.Runtime
