import InitECandidate.Runtime.ReturnedStorePlanMemory
import InitECandidate.Runtime.DecodeStepScratchRecordFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_extension_stores_returned_metadata {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (record arr p n nibs count leaf : BitVec 64)
    (at_rec : s.locals.lookup (ofString "rec") = some (.val (.word record)))
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (at_cn : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState s decodeStepExtensionStores = (some (.returned value),post)) :
    post.memory (record+8) = .word 1 ∧
    post.memory (record+24) = .word arr ∧
    post.memory (record+48) = .word p ∧
    post.memory (record+56) = .word n ∧
    post.memory (record+64) = .word nibs ∧
    post.memory (record+72) = .word count := by
  have supported : BoundReturnedStorePlan (F := F) s.locals decodeStepExtensionStores [(record+8,1),(record+24,arr),(record+48,p),(record+56,n),(record+64,nibs),(record+72,count)] := by
    rw [source_decodeStep_extension_stores]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec,at_arr,at_p,at_n,at_cn]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec,at_arr,at_p,at_n,at_cn]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec,at_arr,at_p,at_n,at_cn]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec,at_arr,at_p,at_n,at_cn]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec,at_arr,at_p,at_n,at_cn]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec,at_arr,at_p,at_n,at_cn]
    exact .finish _ rfl
  have memory := evaluate_bound_returned_store_plan_memory supported s post value rfl run
  rw [memory]
  simp [storePlanMemory,Function.update]

#print axioms decode_step_extension_stores_returned_metadata

theorem decode_step_branch_stores_returned_metadata {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (record arr p n br : BitVec 64)
    (at_rec2 : s.locals.lookup (ofString "rec2") = some (.val (.word record)))
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (at_br : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (value : ValueHOL 64) (run : evaluateHOLFiniteState s decodeStepBranchStores = (some (.returned value),post)) :
    post.memory (record+8) = .word 2 ∧
    post.memory (record+16) = .word br ∧
    post.memory (record+24) = .word arr ∧
    post.memory (record+32) = .word 0 ∧
    post.memory (record+40) = .word 0 ∧
    post.memory (record+48) = .word p ∧
    post.memory (record+56) = .word n := by
  have supported : BoundReturnedStorePlan (F := F) s.locals decodeStepBranchStores [(record+8,2),(record+16,br),(record+24,arr),(record+32,0),(record+40,0),(record+48,p),(record+56,n)] := by
    rw [source_decode_step_branch_stores_frame]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec2,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec2,at_arr,at_p,at_n,at_br]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec2,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec2,at_arr,at_p,at_n,at_br]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec2,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec2,at_arr,at_p,at_n,at_br]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec2,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec2,at_arr,at_p,at_n,at_br]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec2,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec2,at_arr,at_p,at_n,at_br]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec2,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec2,at_arr,at_p,at_n,at_br]
    apply BoundReturnedStorePlan.store
    · intro state locals
      simp [evalHOLExact,evalListHOLExact,locals,at_rec2,wordOpHOL,wordOp,valueIsWord,valueWord]
    · intro state locals
      simp [evalHOLExact,locals,at_rec2,at_arr,at_p,at_n,at_br]
    exact .finish _ rfl
  have memory := evaluate_bound_returned_store_plan_memory supported s post value rfl run
  rw [memory]
  simp [storePlanMemory,Function.update]

#print axioms decode_step_branch_stores_returned_metadata
end InitECandidate.Runtime
