import InitECandidate.Runtime.DecodeStepTwoCasePushFrame
import InitECandidate.Runtime.DecodeStepListPushProgress
import InitECandidate.Runtime.DecodeStepTwoCasePushProgress
import InitECandidate.Runtime.DecodeStepBranchUniformBound
import InitECandidate.Runtime.PanDecReturnedScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned push from the actual list-node dispatch consumes 88 scratch
bytes for both supported arities. Unsupported arities cannot return a push.
The first slice's bounds are recovered from the actual input-bounded table. -/
theorem decode_step_list_push_returned_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (array count input inputLength scratch frame record : BitVec 64)
    (ceiling inputLimit : Nat)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepListPushCost inputLimit ≤ s.clock)
    (run : evaluateHOLFiniteState s (decodeStepAt 6) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  by_cases two : count = 2
  · subst count
    obtain ⟨pointer,length,entry⟩ := table 0 (by decide)
    have lengthBound : length.toNat ≤ inputLimit :=
      (entry.length_bound s array 0 pointer length input inputLength).trans inputBound
    have product : length.toNat*((2*length.toNat+1)*15+19) ≤ inputLimit*((2*inputLimit+1)*15+19) :=
      Nat.mul_le_mul lengthBound (by omega)
    have divided : length.toNat / 4 ≤ inputLimit / 4 := Nat.div_le_div_right lengthBound
    rw [evaluate_decode_step_two_items s array atSlices] at run
    exact decode_step_two_case_push_returned_frame s post array pointer length scratch frame record ceiling inputLimit
      atArray entry.readable entry.noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
      scratchBelow arena (by unfold decodeStepListPushCost at budget; omega) run
  · by_cases seventeen : count = 17
    · subst count
      rw [evaluate_decode_step_seventeen s array atSlices] at run
      have frameKept := evaluate_decoder_frame_global s decodeStepBranchConstruction decode_step_branch_construction_frame_check code
      rw [run] at frameKept
      exact frameKept.trans frameGlobal
    · rw [evaluate_decode_step_invalid_arity s array count two seventeen code atSlices] at run
      have noReturn := evaluate_discard_call_no_return s (ofString "mpt_fail") [.const 4]
        (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])
      exact False.elim (noReturn (congrArg Prod.fst run))

/-- The actual array declaration preserves the list table and introduces no
clock cost before the original list dispatch. -/
theorem decode_step_array_push_returned_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (array count input inputLength scratch frame record : BitVec 64)
    (ceiling inputLimit : Nat)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (table : RlpSliceInputPrefix s array input inputLength count.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepListPushCost inputLimit ≤ s.clock)
    (run : evaluateHOLFiniteState s (decodeStepAt 5) =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  rw [source_decode_step_array] at run
  obtain ⟨value,output,evaluated,bodyRun,postEq⟩ := evaluate_dec_returned_scope s post (ofString "arr") .one
    (.rfield 0 (.var .local (ofString "sl"))) (decodeStepAt 6) _ run
  have evalArray : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.rfield 0 (.var .local (ofString "sl"))) = some (.val (.word array)) := by
    simp [evalHOLExact,atSlices]
  rw [evalArray] at evaluated
  cases evaluated
  let entered := setVarHOLFinite (ofString "arr") (.val (.word array)) s
  have enteredTable : RlpSliceInputPrefix entered array input inputLength count.toNat := by
    intro index inside
    obtain ⟨p,n,entry⟩ := table index inside
    exact ⟨p,n,entry.after_frame _ _ _ _ _ _ _ _ rfl rfl rfl⟩
  have result := decode_step_list_push_returned_frame entered output array count input inputLength scratch frame record
    ceiling inputLimit (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "arr" ≠ ofString "sl" by decide] using atSlices)
    enteredTable inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget bodyRun
  rw [postEq]
  exact result

#print axioms decode_step_array_push_returned_frame
#print axioms decode_step_list_push_returned_frame
end InitECandidate.Runtime
