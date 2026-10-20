import InitECandidate.Runtime.FrameNewSource
import InitECandidate.Runtime.ReturnedStorePlanMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_frame_new_local_address {F : Type} (s : PanSemStateFiniteExact 64 F)
 (name : MlS) (base offset : BitVec 64) (atBase : s.locals.lookup name=some (.val (.word base))) :
 @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) (frameNewLocalAddress name offset)=
 some (.val (.word (base+offset))) := by
 simp [frameNewLocalAddress,evalHOLExact,evalListHOLExact,atBase,wordOpHOL,wordOp,valueIsWord,valueWord]

/-- An actual returned record store resumes from its exact single-word write;
any inaccessible destination is excluded by the real returned execution. -/
theorem frame_new_store_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record offset word : BitVec 64) (expression : ExpHOL 64) (tail : ProgHOL 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "e")=some (.val (.word record)))
 (evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) expression=some (.val (.word word)))
 (run : evaluateHOLFiniteState s (.seq (.store (frameNewLocalAddress (ofString "e") offset) expression) tail)=(some (.returned value),post)) :
 evaluateHOLFiniteState (sourceWriteWord s (record+offset) word) tail=(some (.returned value),post) := by
 obtain ⟨middle,normal,tailRun⟩:=seq_returned_of_nonreturning_first
  (by intro v;exact evaluate_noDirectReturn _ rfl s v) run
 have address:=eval_frame_new_local_address s (ofString "e") record offset atRecord
 have equal:=store_normal_exact s middle _ _ _ _ address evaluated normal
 subst middle
 exact tailRun

/-- The real returned load/store prefix supplies its readable source cell;
only the concrete typed value of that old cell is required, not readability. -/
theorem frame_new_load_store_returned {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (record offset base sourceOffset word : BitVec 64) (sourceName : MlS) (tail : ProgHOL 64) (value : ValueHOL 64)
 (atRecord : s.locals.lookup (ofString "e")=some (.val (.word record)))
 (atBase : s.locals.lookup sourceName=some (.val (.word base)))
 (atValue : s.memory (base+sourceOffset)=.word word)
 (run : evaluateHOLFiniteState s (.seq (.store (frameNewLocalAddress (ofString "e") offset)
  (.load .one (frameNewLocalAddress sourceName sourceOffset))) tail)=(some (.returned value),post)) :
 evaluateHOLFiniteState (sourceWriteWord s (record+offset) word) tail=(some (.returned value),post) := by
 classical
 have sourceAddress:=eval_frame_new_local_address s sourceName base sourceOffset atBase
 by_cases readable : s.memaddrs (base+sourceOffset)
 · apply frame_new_store_returned s post record offset word _ tail value atRecord _ run
   rw [evalHOLExact,sourceAddress]
   simp [isWfShapeExactHOL,memLoadHOLExact,toExact,readable,atValue]
 · obtain ⟨middle,normal,tailRun⟩:=seq_returned_of_nonreturning_first
    (by intro v;exact evaluate_noDirectReturn _ rfl s v) run
   have sourceFails : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
    (.load .one (frameNewLocalAddress sourceName sourceOffset))=none := by
    rw [evalHOLExact,sourceAddress]
    simp [isWfShapeExactHOL,memLoadHOLExact,toExact,readable]
   have destination:=eval_frame_new_local_address s (ofString "e") record offset atRecord
   rw [evaluateHOLFiniteState_store,destination,sourceFails] at normal
   cases normal
#print axioms eval_frame_new_local_address
#print axioms frame_new_store_returned
#print axioms frame_new_load_store_returned
end InitECandidate.Runtime
