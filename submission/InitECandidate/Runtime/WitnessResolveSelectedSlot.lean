import InitECandidate.Runtime.WitnessSelectedSlot
import InitECandidate.Runtime.WitnessResolveModeSource
import InitECandidate.Runtime.AvoidsLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
 theorem witness_resolve_mode_normal_slot_kept {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode=(none,post)) :
    post.locals.lookup (ofString "slot")=s.locals.lookup (ofString "slot") := by
  have supported : avoidsLocal (ofString "slot") decodeWitnessNodeResolveMode=true := by
    rw [source_witness_resolve_mode,source_witness_resolve_call,source_witness_resolve_tail]
    decide
  have kept := evaluate_avoidsLocal_flowing (ofString "slot") decodeWitnessNodeResolveMode supported s
    (by rw [run];exact Or.inl rfl)
  rw [run] at kept
  exact kept
/-- Actual resolver changes only the top hash word of a live record. Concrete
stage/index frames and the actual unchanged slot retain the selector. -/
theorem WitnessSelectedSlot.after_record_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record : BitVec 64) (selected : WitnessSelectedSlot s record)
    (slotFrame : post.locals.lookup (ofString "slot")=s.locals.lookup (ofString "slot"))
    (stageFrame : post.memory (record+8)=s.memory (record+8))
    (indexFrame : post.memory (record+32)=s.memory (record+32)) : WitnessSelectedSlot post record := by
  rcases selected with ⟨stage,slot⟩ | ⟨stage,index,cell,slot,bound⟩
  · exact Or.inl ⟨stageFrame.trans stage,slotFrame.trans slot⟩
  · exact Or.inr ⟨stageFrame.trans stage,index,indexFrame.trans cell,slotFrame.trans slot,bound⟩
 theorem witness_resolve_mode_normal_selected_slot {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record : BitVec 64) (selected : WitnessSelectedSlot s record)
    (stageFrame : post.memory (record+8)=s.memory (record+8))
    (indexFrame : post.memory (record+32)=s.memory (record+32))
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode=(none,post)) : WitnessSelectedSlot post record :=
  selected.after_record_frame s post record (witness_resolve_mode_normal_slot_kept s post run) stageFrame indexFrame
#print axioms witness_resolve_mode_normal_slot_kept
#print axioms WitnessSelectedSlot.after_record_frame
#print axioms witness_resolve_mode_normal_selected_slot
end InitECandidate.Runtime
