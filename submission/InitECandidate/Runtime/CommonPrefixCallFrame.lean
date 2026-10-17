import InitECandidate.Runtime.CommonPrefixCallResult
import InitECandidate.Runtime.CommonPrefixReadFrame
import InitECandidate.Runtime.OriginalCommonPrefixCode
import InitECandidate.Runtime.PanFourWordLookup
import InitECandidate.Runtime.PanDecCallNormalReturnFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the actual prefix declaration-call binds a word no
larger than either input length before executing its arbitrary continuation. -/
theorem evaluate_commonPrefix_decCall_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (arguments : List (ExpHOL 64)) (continuation : ProgHOL 64)
    (a left b right : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word a),.val (.word left),.val (.word b),.val (.word right)])
    (code : state.code = originalRuntimeCode)
    (ticks : (wordMin left right).toNat + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state (.decCall name .one (ofString "common_prefix_length") arguments continuation) = (none,post)) :
    ∃ (found : BitVec 64) (ready output : PanSemStateFiniteExact 64 F), found.toNat ≤ left.toNat ∧ found.toNat ≤ right.toNat ∧
      ready.locals = state.locals ∧ ready.memory = state.memory ∧ ready.globals = state.globals ∧
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
  have bodyFrame : ∀ result output, evaluateHOLFiniteState entry
      (sourceFunctionBody Guest.guestFn_common_prefix_length) = (result,output) →
      output.memory = state.memory ∧ output.globals = state.globals := by
    intro result output evaluated
    have frame := evaluate_commonPrefix_body_read_frame entry left right leftLocal rightLocal code
    rw [evaluated] at frame
    exact frame
  obtain ⟨value,ready,output,valid,locals,memory,globals,tail,restored⟩ := evaluate_decCall_normal_return_frame
    state post name (ofString "common_prefix_length") .one .one arguments
    [.val (.word a),.val (.word left),.val (.word b),.val (.word right)]
    (sourceFunctionBody Guest.guestFn_common_prefix_length) continuation callee args lookup property bodyProperty bodyFrame run
  obtain ⟨found,rfl,leftBound,rightBound⟩ := valid
  exact ⟨found,ready,output,leftBound,rightBound,locals,memory,globals,tail,restored⟩

#print axioms evaluate_commonPrefix_decCall_normal_frame
end InitECandidate.Runtime
