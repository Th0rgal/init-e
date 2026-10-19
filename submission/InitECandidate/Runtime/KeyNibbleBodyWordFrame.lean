import InitECandidate.Runtime.NibbleLoopWordFrame
import InitECandidate.Runtime.OriginalKeyToNibblesCode
import InitECandidate.Runtime.PanThreeWordLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- All outcomes of the original conversion preserve a word outside its
output interval; source/output accessibility and sufficient fuel are not assumed. -/
theorem evaluate_keyNibble_body_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (length out watched : BitVec 64) (small : length.toNat + 4 < 2^64)
    (atN : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atOut : s.locals.lookup (ofString "out") = some (.val (.word out)))
    (separate : ∀ offset : Nat, offset < 2 * length.toNat →
      watched ≠ panByteAlignHOL (out + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_key_to_nibbles)).2.memory watched =
      s.memory watched := by
  let entered := setVarHOLFinite (ofString "i") (.val (.word (0#64))) s
  have initial : NibbleWordInvariant entered length out := by
    refine ⟨⟨0,?_,by simp⟩,?_,?_⟩
    · simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "i" ≠ ofString "n" by decide] using atN
    · simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "i" ≠ ofString "out" by decide] using atOut
  have main := evaluate_keyNibble_main_loop_word_frame entered length out watched small initial separate
  rw [source_keyToNibbles_body,evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  change (evaluateHOLFiniteState entered (.seq keyToNibblesMainLoop
    (.seq keyToNibblesTailLoop (.return (.const 0))))).2.memory watched = s.memory watched
  rw [evaluateHOLFiniteState_seq_line780]
  cases mainRun : evaluateHOLFiniteState entered keyToNibblesMainLoop with
  | mk result middle =>
    rw [mainRun] at main
    dsimp only at main ⊢
    cases result with
    | some stopped => exact main.1
    | none =>
      have tail := evaluate_keyNibble_tail_loop_word_frame middle length out watched small (main.2 rfl) separate
      rw [evaluateHOLFiniteState_seq_line780]
      cases tailRun : evaluateHOLFiniteState middle keyToNibblesTailLoop with
      | mk result post =>
        rw [tailRun] at tail
        dsimp only at tail ⊢
        cases result with
        | some stopped => exact tail.1.trans main.1
        | none =>
          exact (congrFun (evaluate_readOnly_memory (.return (.const 0)) rfl post) watched).trans
            (tail.1.trans main.1)

theorem evaluate_keyNibble_call_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (keyArgument sizeArgument outputArgument : ExpHOL 64) (key length out watched : BitVec 64)
    (small : length.toNat + 4 < 2^64) (code : s.code = originalRuntimeCode)
    (args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [keyArgument,sizeArgument,outputArgument] = some [.val (.word key),.val (.word length),.val (.word out)])
    (separate : ∀ offset : Nat, offset < 2 * length.toNat →
      watched ≠ panByteAlignHOL (out + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState s (.call (some (none,none)) (ofString "key_to_nibbles")
      [keyArgument,sizeArgument,outputArgument])).2.memory watched = s.memory watched := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "key",.val (.word key))).update
      (ofString "n",.val (.word length))).update (ofString "out",.val (.word out))
  let entry := callEntryStateHOLFinite s callee
  have atN : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "out" ≠ ofString "n" by decide]
  have atOut : entry.locals.lookup (ofString "out") = some (.val (.word out)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have frame := evaluate_keyNibble_body_word_frame entry length out watched small atN atOut separate
  have lookup := pan_three_word_lookup s.code.lookup (ofString "key_to_nibbles")
    (ofString "key") (ofString "n") (ofString "out")
    (sourceFunctionBody Guest.guestFn_key_to_nibbles) key length out
    (by decide) (by decide) (by decide) (by rw [code]; exact originalRuntimeCode_keyToNibbles_lookup)
  simp only [evaluateHOLFiniteState_call,args]
  rw [lookup]
  dsimp only
  by_cases empty : s.clock = 0
  · simp [empty,emptyLocalsHOLFinite]
  · rw [if_neg empty]
    cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_key_to_nibbles) with
    | mk result post =>
      rw [bodyRun] at frame
      change post.memory watched = s.memory watched at frame
      cases result with
      | none => exact frame
      | some result =>
        cases result <;> simp_all [emptyLocalsHOLFinite]
        split <;> exact frame

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_keyNibble_body_word_frame
#print axioms InitECandidate.Runtime.evaluate_keyNibble_call_word_frame
