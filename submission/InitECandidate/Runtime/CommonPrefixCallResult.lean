import InitECandidate.Runtime.CommonPrefixOriginalBodyBound
import InitECandidate.Runtime.OriginalCommonPrefixCode
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.PanDecCallNormalReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def commonPrefixCallee (a left b right : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (((HolFiniteMapExact.empty.update (ofString "a",.val (.word a))).update (ofString "al",.val (.word left))).update
    (ofString "b",.val (.word b))).update (ofString "bl",.val (.word right))

/-- Normal completion of the actual prefix declaration-call binds a word no
larger than either input length before executing its arbitrary continuation. -/
theorem evaluate_commonPrefix_decCall_normal_result {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (a left b right : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word a),.val (.word left),.val (.word b),.val (.word right)])
    (code : state.code = originalRuntimeCode)
    (ticks : (wordMin left right).toNat + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "common_prefix_length") arguments continuation) = (none,post)) :
    ∃ (found : BitVec 64) (ready output : PanSemStateFiniteExact 64 F), found.toNat ≤ left.toNat ∧ found.toNat ≤ right.toNat ∧
      ready.locals = state.locals ∧
      evaluateHOLFiniteState (setVarHOLFinite name (.val (.word found)) ready) continuation = (none,output) ∧
      post = {output with locals := HolFiniteMapExact.resVarEq output.locals (name,state.locals.lookup name)} := by
  let callee := commonPrefixCallee a left b right
  let entry := callEntryStateHOLFinite state callee
  have leftLocal : entry.locals.lookup (ofString "al") = some (.val (.word left)) := by
    simp [entry,callEntryStateHOLFinite,callee,commonPrefixCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "bl" ≠ ofString "al" by decide,show ofString "b" ≠ ofString "al" by decide]
  have rightLocal : entry.locals.lookup (ofString "bl") = some (.val (.word right)) := by
    simp [entry,callEntryStateHOLFinite,callee,commonPrefixCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨bodyResult,bodyPost,bodyRun,_,_,_,returned⟩ := evaluate_original_commonPrefix_body_bounded
    entry left right leftLocal rightLocal code (by change (wordMin left right).toNat + 1 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "common_prefix_length") =
      some ([(ofString "a",.one),(ofString "al",.one),(ofString "b",.one),(ofString "bl",.one)],
        sourceFunctionBody Guest.guestFn_common_prefix_length,.one) := by
    rw [code]; exact originalRuntimeCode_commonPrefix_lookup
  have lookup := pan_four_word_lookup state.code.lookup (ofString "common_prefix_length")
    (ofString "a") (ofString "al") (ofString "b") (ofString "bl")
    (sourceFunctionBody Guest.guestFn_common_prefix_length) a left b right
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) installed
  let property := fun value : ValueHOL 64 => ∃ found : BitVec 64,
    value = .val (.word found) ∧ found.toNat ≤ left.toNat ∧ found.toNat ≤ right.toNat
  have bodyProperty : ∀ value output, evaluateHOLFiniteState entry
      (sourceFunctionBody Guest.guestFn_common_prefix_length) = (some (.returned value),output) → property value := by
    intro value output evaluated
    have same := (Prod.mk.inj (bodyRun.symm.trans evaluated)).1
    exact returned value same
  obtain ⟨value,ready,output,valid,locals,tail,restored⟩ := evaluate_decCall_normal_return_property
    state post name (ofString "common_prefix_length") .one .one arguments
    [.val (.word a),.val (.word left),.val (.word b),.val (.word right)]
    (sourceFunctionBody Guest.guestFn_common_prefix_length) continuation callee args lookup property bodyProperty run
  obtain ⟨found,rfl,leftBound,rightBound⟩ := valid
  exact ⟨found,ready,output,leftBound,rightBound,locals,tail,restored⟩

/-- A prefix bounded by the remaining key cannot advance beyond the key,
with subtraction interpreted under the insertion level invariant. -/
theorem commonPrefix_result_fits_remaining_key (level length found : BitVec 64)
    (levelBound : level.toNat ≤ length.toNat)
    (prefixBound : found.toNat ≤ (length - level).toNat) :
    level.toNat + found.toNat ≤ length.toNat := by
  rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr levelBound)] at prefixBound
  omega

#print axioms commonPrefix_result_fits_remaining_key
#print axioms evaluate_commonPrefix_decCall_normal_result
end InitECandidate.Runtime
