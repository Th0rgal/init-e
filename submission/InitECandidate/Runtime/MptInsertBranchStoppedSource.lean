import InitECandidate.Runtime.MptInsertRunningChoice
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every normal branch advance reaches the actual final go=1 assignment. -/
theorem mpt_insert_branch_advance_normal_go {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (run : evaluateHOLFiniteState s mptInsertBranchAdvance=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) := by
 rw [source_mptInsert_branch_advance] at run
 obtain ⟨s1,_,run1⟩:=seq_normal_parts run
 obtain ⟨s2,_,run2⟩:=seq_normal_parts run1
 obtain ⟨s3,_,run3⟩:=seq_normal_parts run2
 obtain ⟨s4,_,run4⟩:=seq_normal_parts run3
 rw [evaluateHOLFiniteState_assign] at run4
 simp only [evalHOLExact] at run4
 split at run4
 · have same:=(Prod.mk.inj run4).2.symm
   rw [same]
   simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
 · cases run4

theorem mpt_insert_branch_descent_normal_go {F : Type}
 (s post : PanSemStateFiniteExact 64 F)
 (run : evaluateHOLFiniteState s mptInsertBranchDescent=(none,post)) :
 post.locals.lookup (ofString "go")=some (.val (.word (1#64))) := by
 rw [source_mptInsert_branch_descent] at run
 obtain ⟨value,output,_,advance,scope⟩:=evaluate_dec_normal_scope s post (ofString "idx") .one _ _ run
 have go:=mpt_insert_branch_advance_normal_go _ output advance
 rw [scope,saved_local_lookup_other _ (ofString "idx") (ofString "go") _ (by decide)]
 exact go

/-- A stopped normal branch dispatch must have consumed the whole key and
selected the actual payload-update arm. This uses no memory or future-run premise. -/
theorem mpt_insert_branch_dispatch_stopped {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (level length : BitVec 64)
 (atLevel : s.locals.lookup (ofString "level")=some (.val (.word level)))
 (atLength : s.locals.lookup (ofString "klen")=some (.val (.word length)))
 (stopped : post.locals.lookup (ofString "go")=some (.val (.word (0#64))))
 (run : evaluateHOLFiniteState s mptInsertBranchDispatch=(none,post)) :
 level=length ∧evaluateHOLFiniteState s mptInsertBranchValue=(none,post) := by
 have cmp : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a))
  (.cmp .equal (.var .local (ofString "level")) (.var .local (ofString "klen")))=
  some (.val (.word (if level=length then 1#64 else 0#64))) := by
  simp [evalHOLExact,atLevel,atLength,Compiler.Encoders.Asm.wordCmpHOL]
 rw [source_mptInsert_branch_dispatch,evaluateHOLFiniteState_ite,cmp] at run
 by_cases same : level=length
 · exact ⟨same,by simpa only [if_pos same,show (1#64)≠0 from by decide,if_false] using run⟩
 · have descent : evaluateHOLFiniteState s mptInsertBranchDescent=(none,post) := by
    simpa only [if_neg same,show (0#64)=0 from rfl,if_true] using run
   have go:=mpt_insert_branch_descent_normal_go s post descent
   rw [stopped] at go
   cases go

#print axioms mpt_insert_branch_advance_normal_go
#print axioms mpt_insert_branch_descent_normal_go
#print axioms mpt_insert_branch_dispatch_stopped
end InitECandidate.Runtime
