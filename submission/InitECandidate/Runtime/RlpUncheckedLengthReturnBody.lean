import InitECandidate.Runtime.RlpReadLengthCallResult
import InitECandidate.Runtime.PanDecCallReturnedWordBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The long unchecked branches return exactly one prefix byte plus the
length-of-length and the word decoded by the actual reader declaration. -/
theorem rlpUnchecked_length_declaration_return_body {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (lengthName resultName : MlS) (different : resultName ≠ lengthName)
    (arguments : List (ExpHOL 64)) (pointer length : BitVec 64) (value : ValueHOL 64)
    (lengthLocal : state.locals.lookup lengthName = some (.val (.word length)))
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (.decCall resultName .one (ofString "rlp_read_length") arguments
      (.return (.op .add [.const 1,.var .local lengthName,.var .local resultName]))) = (some (.returned value),post)) :
    ∃ (decoded : BitVec 64) (bodyPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite state (rlpReadLengthCallee pointer length))
        (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned (.val (.word decoded))),bodyPost) ∧
      value = .val (.word (1 + (length + decoded))) := by
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) pointer length (by decide) installed
  obtain ⟨decoded,bodyPost,ready,output,bodyRun,locals,tail,_⟩ := evaluate_decCall_one_returned_word_body state post resultName (ofString "rlp_read_length")
    arguments [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_read_length)
    (.return (.op .add [.const 1,.var .local lengthName,.var .local resultName])) (rlpReadLengthCallee pointer length) args lookup value run
  let entered := setVarHOLFinite resultName (.val (.word decoded)) ready
  have atLength : entered.locals.lookup lengthName = some (.val (.word length)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,locals] using lengthLocal
  have atDecoded : entered.locals.lookup resultName = some (.val (.word decoded)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have actual : evaluateHOLFiniteState entered (.return (.op .add [.const 1,.var .local lengthName,.var .local resultName])) =
      (some (.returned (.val (.word (1 + (length + decoded))))),emptyLocalsHOLFinite entered) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atLength,atDecoded,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact]
  have same := (Prod.mk.inj (tail.symm.trans actual)).1
  exact ⟨decoded,bodyPost,bodyRun,PanSemResultExact.returned.inj (Option.some.inj same)⟩

#print axioms rlpUnchecked_length_declaration_return_body
end InitECandidate.Runtime
