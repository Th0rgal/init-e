import InitECandidate.Runtime.MainNormalSuffixNoDomainBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- A wrongly shaped success value fails the actual serializer argument check,
or an earlier unreadable chain-cell load; neither path spends a source tick. -/
theorem main_normal_suffix_invalid_success {F : Type} (s : PanSemStateFiniteExact 64 F)
 (output root si : BitVec 64) (success : ValueHOL 64)
 (atOutput : s.locals.lookup (ofString "out")=some (.val (.word output)))
 (atRoot : s.locals.lookup (ofString "root")=some (.val (.word root)))
 (atSuccess : s.locals.lookup (ofString "succ")=some success)
 (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
 (wrong : shapeEqHOL .one (shapeOfHOLExact success)=false)
 (code : s.code=originalRuntimeCode) :
 evaluateHOLFiniteState s (mainAt 24)=(some .error,s) := by
 by_cases domain : s.memaddrs (si+88#64)
 · cases cell : s.memory (si+88#64) with
   | word chain=>
    have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) mainNormalSerializeArguments=
     some [.val (.word output),.val (.word root),success,.val (.word chain),.val (.word (5377#64))] := by
     rw [evalListHOLFinite_eq_toExact]
     simp [mainNormalSerializeArguments,evalListHOLExact,evalHOLExact,atOutput,atRoot,atSuccess,atSi,
      wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,cell]
    have lookup : lookupCodeHOLFinite s.code.lookup (ofString "serialize_result")
     [.val (.word output),.val (.word root),success,.val (.word chain),.val (.word (5377#64))]=none := by
     rw [code]
     rw [PanSemStateFiniteExact.lookupCodeHOLFinite_eq_none_iff]
     unfold Flapjack.lookupCodeHOLExact
     rw [originalRuntimeCode_serializeResult_lookup]
     simp [shapeOfHOLExact,wrong,shapeEqHOL]
    rw [source_main_normal_serialization,mainNormalSerialization]
    exact evaluateHOLFiniteState_decCall_lookup_none s (ofString "n") .one (ofString "serialize_result")
     mainNormalSerializeArguments mainNormalOutput _ args lookup
 · have args : evalListHOLFinite s (h:=fun a=>Classical.propDecidable (s.memaddrs a)) mainNormalSerializeArguments=none := by
    rw [evalListHOLFinite_eq_toExact]
    simp [mainNormalSerializeArguments,evalListHOLExact,evalHOLExact,atOutput,atRoot,atSuccess,atSi,
     wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain]
   rw [source_main_normal_serialization,mainNormalSerialization]
   exact evaluateHOLFiniteState_decCall_args_none s (ofString "n") .one (ofString "serialize_result")
    mainNormalSerializeArguments mainNormalOutput args

/-- The actual output suffix is bounded for every returned success value.
Word returns use the serializer bound; struct returns fail its real shape check. -/
theorem runBounded_main_normal_suffix_any_success {F : Type} (s : PanSemStateFiniteExact 64 F)
 (output root si : BitVec 64) (success : ValueHOL 64)
 (atOutput : s.locals.lookup (ofString "out")=some (.val (.word output)))
 (atRoot : s.locals.lookup (ofString "root")=some (.val (.word root)))
 (atSuccess : s.locals.lookup (ofString "succ")=some success)
 (atSi : s.locals.lookup (ofString "si")=some (.val (.word si)))
 (code : s.code=originalRuntimeCode) (budget : 65≤s.clock) : RunBounded s (mainAt 24) 65 := by
 cases success with
 | val value=>
  cases value with
  | word word=>exact runBounded_main_normal_suffix_no_domain s output root word si atOutput atRoot atSuccess atSi code budget
 | rStruct fields=>
  have error:=main_normal_suffix_invalid_success s output root si (.rStruct fields) atOutput atRoot atSuccess atSi (by simp [shapeEqHOL,shapeOfHOLExact]) code
  unfold RunBounded;rw [error];simp
 | nStruct size fields=>
  have error:=main_normal_suffix_invalid_success s output root si (.nStruct size fields) atOutput atRoot atSuccess atSi (by simp [shapeEqHOL,shapeOfHOLExact]) code
  unfold RunBounded;rw [error];simp
#print axioms main_normal_suffix_invalid_success
#print axioms runBounded_main_normal_suffix_any_success
end InitECandidate.Runtime
