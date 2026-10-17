import InitECandidate.Runtime.KeyToNibbles32BodyBound
import InitECandidate.Runtime.OriginalKeyToNibblesCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real runtime call converting a 32-byte key costs at most nine source
ticks, for all key/output pointers and every byte-access outcome. -/
theorem evaluate_keyToNibbles32_call_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyArgument sizeArgument outputArgument : ExpHOL 64) (key output : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [keyArgument,sizeArgument,outputArgument] = some [.val (.word key),.val (.word (32 : BitVec 64)),.val (.word output)])
    (ticks : 9 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "key_to_nibbles") [keyArgument,sizeArgument,outputArgument]);
    state.clock ≤ evaluated.2.clock + 9 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "key",.val (.word key))).update (ofString "n",.val (.word (32 : BitVec 64)))).update (ofString "out",.val (.word output))
  let entry := callEntryStateHOLFinite state callee
  have localN : entry.locals.lookup (ofString "n") = some (.val (.word (32 : BitVec 64))) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "out" ≠ ofString "n" from by decide]
  obtain ⟨result,post,body,cost,remaining,noTimeout⟩ := evaluate_keyToNibbles32_body_bounded entry localN
    (by change 8 ≤ state.clock - 1; omega)
  have postCost : state.clock ≤ post.clock + 9 := by
    change state.clock - 1 ≤ post.clock + 8 at cost
    omega
  have postRemaining : post.clock ≤ state.clock := by
    change post.clock ≤ state.clock - 1 at remaining
    omega
  have installed : state.code.lookup (ofString "key_to_nibbles") =
      some ([(ofString "key",.one),(ofString "n",.one),(ofString "out",.one)],sourceFunctionBody Guest.guestFn_key_to_nibbles,.one) := by
    rw [code]
    exact originalRuntimeCode_keyToNibbles_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "key_to_nibbles") (ofString "key") (ofString "n") (ofString "out")
    (sourceFunctionBody Guest.guestFn_key_to_nibbles) key (32 : BitVec 64) output (by decide) (by decide) (by decide) installed
  have nonzero : state.clock ≠ 0 := by omega
  simp only [evaluateHOLFiniteState_call,args]
  rw [lookup]
  dsimp only
  rw [if_neg nonzero,body]
  cases result with
  | none => exact ⟨postCost,postRemaining,by simp⟩
  | some result =>
    cases result <;> simp_all [emptyLocalsHOLFinite]
    split <;> simp_all


#print axioms evaluate_keyToNibbles32_call_bounded
end InitECandidate.Runtime
