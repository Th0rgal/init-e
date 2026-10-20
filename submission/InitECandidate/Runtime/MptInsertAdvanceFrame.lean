import InitECandidate.Runtime.MptInsertAdvance
import InitECandidate.Runtime.HtabDelBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

private theorem local_assignment_normal_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (name : MlS) (source : ExpHOL 64)
 (run : evaluateHOLFiniteState s (.assign .local name source)=(none,post)) :
 post.memory=s.memory ∧post.globals=s.globals := by
 rw [evaluateHOLFiniteState_assign] at run
 cases evaluated : @evalHOLExact 64 F _ s.toExact (fun a=>Classical.propDecidable (s.memaddrs a)) source with
 | none => rw [evaluated] at run;cases run
 | some value =>
   rw [evaluated] at run
   dsimp only at run
   split at run
   · have same:=(Prod.mk.inj run).2.symm
     rw [same]
     exact ⟨rfl,rfl⟩
   · cases run

/-- The actual final traversal assignments preserve memory and globals in
any normal execution, without assumptions about future locals or callees. -/
theorem mpt_insert_advance_normal_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
 (run : evaluateHOLFiniteState s mptInsertAdvance=(none,post)) :
 post.memory=s.memory ∧post.globals=s.globals := by
 rw [source_mptInsert_advance] at run
 obtain ⟨first,step1,tail1⟩:=seq_normal_parts run
 obtain ⟨second,step2,step3⟩:=seq_normal_parts tail1
 have frame1:=local_assignment_normal_frame s first _ _ step1
 have frame2:=local_assignment_normal_frame first second _ _ step2
 have frame3:=local_assignment_normal_frame second post _ _ step3
 exact ⟨frame3.1.trans (frame2.1.trans frame1.1),frame3.2.trans (frame2.2.trans frame1.2)⟩

#print axioms mpt_insert_advance_normal_frame
end InitECandidate.Runtime
