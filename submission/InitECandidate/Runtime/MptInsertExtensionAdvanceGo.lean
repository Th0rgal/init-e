import InitECandidate.Runtime.MptInsertExtensionAdvance
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem normal_sequence_tail {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (first tail : ProgHOL 64)
 (run : evaluateHOLFiniteState s (.seq first tail)=(none,post)) :
 ∃middle,evaluateHOLFiniteState middle tail=(none,post) := by
 rw [evaluateHOLFiniteState_seq_line780] at run
 cases step : evaluateHOLFiniteState s first with
 | mk result middle =>
   rw [step] at run
   cases result with
   | none => exact ⟨middle,run⟩
   | some result => cases run

/-- Any normal execution of the actual matched advance reaches its final
assignment of go=1, regardless of the initial locals or memory. -/
theorem mpt_insert_extension_advance_normal_go {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (run : evaluateHOLFiniteState s mptInsertExtensionAdvance=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) := by
 rw [source_mptInsert_extension_advance] at run
 obtain ⟨s1,run1⟩:=normal_sequence_tail s post _ _ run
 obtain ⟨s2,run2⟩:=normal_sequence_tail s1 post _ _ run1
 obtain ⟨s3,run3⟩:=normal_sequence_tail s2 post _ _ run2
 obtain ⟨s4,run4⟩:=normal_sequence_tail s3 post _ _ run3
 rw [evaluateHOLFiniteState_assign] at run4
 simp only [evalHOLExact] at run4
 split at run4
 · have same := (Prod.mk.inj run4).2.symm
   rw [same]
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · cases run4

#print axioms mpt_insert_extension_advance_normal_go
end InitECandidate.Runtime
