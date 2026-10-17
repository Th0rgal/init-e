import InitECandidate.Runtime.KeyNibbleBodyPreservation
import InitECandidate.Runtime.OriginalKeyToNibblesCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual runtime conversion call costs at most length/4 + 4 source
ticks and produces valid nibbles on normal completion. -/
theorem evaluate_keyToNibbles_general_call_preserves {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument sizeArgument outputArgument : ExpHOL 64) (key output length : BitVec 64)
    (watched watchedLength : BitVec 64)
    (watchedValid : TrieNibbleRange state watched watchedLength)
    (lengthBound : 2 * length.toNat + 8 < 2^64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [keyArgument,sizeArgument,outputArgument] = some [.val (.word key),.val (.word length),.val (.word output)])
    (sourceDomain : ∀ offset : Nat, offset < length.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (outputDomain : ∀ offset : Nat, offset < 2 * length.toNat → state.memaddrs (panByteAlignHOL (output + BitVec.ofNat 64 offset)))
    (ticks : length.toNat / 4 + 4 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "key_to_nibbles") [keyArgument,sizeArgument,outputArgument]);
    state.clock ≤ evaluated.2.clock + (length.toNat / 4 + 4) ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut ∧
      (evaluated.1 = none → TrieNibbleRange evaluated.2 output (2 * length) ∧ TrieNibbleRange evaluated.2 watched watchedLength) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "key",.val (.word key))).update (ofString "n",.val (.word length))).update (ofString "out",.val (.word output))
  let entry := callEntryStateHOLFinite state callee
  have localN : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "out" ≠ ofString "n" from by decide]
  have localKey : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "key" by decide,show ofString "n" ≠ ofString "key" by decide]
  have localOut : entry.locals.lookup (ofString "out") = some (.val (.word output)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨result,post,body,cost,remaining,noTimeout,range⟩ :=
    evaluate_keyToNibbles_general_body_preserves entry key output length watched watchedLength (watchedValid.after_frame rfl rfl rfl) lengthBound localKey localOut sourceDomain outputDomain localN
      (by change length.toNat / 4 + 3 ≤ state.clock - 1; omega)
  have postCost : state.clock ≤ post.clock + (length.toNat / 4 + 4) := by
    change state.clock - 1 ≤ post.clock + (length.toNat / 4 + 3) at cost
    omega
  have postRemaining : post.clock ≤ state.clock := by
    change post.clock ≤ state.clock - 1 at remaining
    omega
  have installed : state.code.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key",.one),(ofString "n",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_key_to_nibbles,.one) := by
    rw [code]
    exact originalRuntimeCode_keyToNibbles_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "key_to_nibbles") (ofString "key") (ofString "n") (ofString "out")
    (sourceFunctionBody Guest.guestFn_key_to_nibbles) key length output (by decide) (by decide) (by decide) installed
  have nonzero : state.clock ≠ 0 := by omega
  simp only [evaluateHOLFiniteState_call,args]
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,body]
  cases result with
  | none => exact ⟨postCost,postRemaining,by simp,by simp⟩
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split
    · refine ⟨postCost,postRemaining,by simp,?_⟩
      intro _
      exact ⟨range.1.after_frame rfl rfl rfl,range.2.after_frame rfl rfl rfl⟩
    · simp_all


#print axioms evaluate_keyToNibbles_general_call_preserves
end InitECandidate.Runtime
