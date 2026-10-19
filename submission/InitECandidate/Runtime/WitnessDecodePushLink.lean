import InitECandidate.Runtime.WitnessDecodePushProgress
import InitECandidate.Runtime.WordStoreNormalMemory
import InitECandidate.Runtime.HtabSetBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def witnessDecodePushAfterLink : ProgHOL 64 :=
  match witnessDecodePush with | .seq _ tail => tail | _ => .skip

theorem source_witness_decode_link : witnessDecodePush =
  .seq (.store (.op .add [.rfield 1 (.var .local (ofString "d")),.const 0]) (.var .local (ofString "top")))
    witnessDecodePushAfterLink := by
  simp only [witnessDecodePushAfterLink,source_witness_decode_push]

/-- The actual push links the new record to the previous top and changes no
other memory word. Slot selection and mode changes cannot corrupt old records. -/
theorem witness_decode_push_normal_link {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record previous : BitVec 64)
    (atD : s.locals.lookup (ofString "d") = some (.rStruct [.val (.word (1#64)),.val (.word record)]))
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word previous)))
    (run : evaluateHOLFiniteState s witnessDecodeTail = (none,post)) :
    post.memory record = .word previous ∧
      ∀ watched : BitVec 64, watched ≠ record → post.memory watched = s.memory watched := by
  have condition : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.rfield 0 (.var .local (ofString "d"))) (.const 0)) = some (.val (.word (0#64))) := by
    simp [evalHOLExact,atD,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_witness_decode_tail,evaluateHOLFiniteState_ite,condition] at run
  change evaluateHOLFiniteState s witnessDecodePush = (none,post) at run
  rw [source_witness_decode_link] at run
  obtain ⟨stored,storeRun,_,tailRun⟩ := evaluate_store_sequence_normal s post _ _ _ run
  have cells := evaluate_word_store_normal_memory s stored _ _ record previous
    (by simp [evalHOLExact,evalListHOLExact,atD,wordOpHOL,wordOp,valueIsWord,valueWord])
    (by simp [evalHOLExact,atTop]) storeRun
  have readOnly : readOnlyMemory witnessDecodePushAfterLink = true := by
    simp only [witnessDecodePushAfterLink,source_witness_decode_push]
    rfl
  have memory := evaluate_readOnly_memory witnessDecodePushAfterLink readOnly stored
  rw [tailRun] at memory
  rw [memory]
  exact cells

#print axioms source_witness_decode_link
#print axioms witness_decode_push_normal_link
end InitECandidate.Runtime
