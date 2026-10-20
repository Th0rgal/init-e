import InitECandidate.Runtime.SourceCostLoopIf
import InitECandidate.Runtime.SourceCostLoopDec
import InitECandidate.Runtime.SourceCostLoopWhile
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Crep statements covered by the checked Crep-to-Loop transfer. -/
def crepLoopCovered : CrepProgHOL 64 → Bool
  | .seq first second | .ite _ first second => crepLoopCovered first && crepLoopCovered second
  | .dec _ _ body | .while _ body => crepLoopCovered body
  | p => (crepLeafWork p).isSome

/-- Crep-to-Loop executed-work transfer, by induction on executed Crep work.
Premises are exactly the original `ncompile_correct` premises. -/
theorem crep_loop_executed_work {F : Type} {t : CrepSemHOLState 64 F} {p : CrepProgHOL 64}
    {w : Nat} (work : CrepWork t p w) :
    ∀ (u : LoopSemStateFiniteExact 64 F) (context : CrepToLoopContextExact) (live : NumSet),
      (evalCrepSemHOLProgExact t p).1 ≠ some .error → CrepLoopRel context live t u →
      crepLoopCovered p = true → LoopPaid context live t u p w := by
  induction work with
  | @seqNext t first second middle firstWork secondWork one run two ihOne ihTwo =>
    intro u context live ok rel covered
    simp only [crepLoopCovered, Bool.and_eq_true] at covered
    have okSeq := ok
    rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
    simp only [if_true] at okSeq
    obtain ⟨e1, w1, work1, bound1, rel1⟩ := ihOne u context live (by rw [run]; simp) rel
      covered.1
    rw [run] at rel1
    obtain ⟨norm1, mid⟩ := rels_of_run rel1 rfl
    rcases hrun1 : evaluate (compileHOLExact context live first)
        { u with clock := u.clock + e1 } with ⟨r1, u1⟩
    rw [hrun1] at work1 norm1 mid
    simp only at norm1 mid
    subst norm1
    obtain ⟨e2, w2, work2, bound2, rel2⟩ := ihTwo u1 context live okSeq mid covered.2
    have lifted := LoopWork.add_clock work1 e2 (by simp)
    simp only [] at lifted
    have combined := LoopWork.seqNext lifted work2
    have state : ({ u with clock := u.clock + (e1 + e2) } : LoopSemStateFiniteExact 64 F) =
        { ({ u with clock := u.clock + e1 } : LoopSemStateFiniteExact 64 F) with
          clock := u.clock + e1 + e2 } := by
      simp [Nat.add_assoc]
    refine ⟨e1 + e2, w1 + w2, ?_, by omega, ?_⟩
    · rw [state]
      have sound := LoopWork.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound]
      exact combined
    · have sound := LoopWork.sound combined
      rw [state]
      simp only [compileHOLExact] at sound ⊢
      rw [sound, evalCrepSemHOLProgExact_seq_holShape, run]
      simp only [if_true]
      exact rel2
  | @seqStop t first second result middle firstWork one run ihOne =>
    intro u context live ok rel covered
    simp only [crepLoopCovered, Bool.and_eq_true] at covered
    obtain ⟨e1, w1, work1, bound1, rel1⟩ := ihOne u context live (by
      have okSeq := ok
      rw [evalCrepSemHOLProgExact_seq_holShape, run] at okSeq
      rw [run]; simpa using okSeq) rel covered.1
    rw [run] at rel1
    rcases hrun1 : evaluate (compileHOLExact context live first)
        { u with clock := u.clock + e1 } with ⟨r1, u1⟩
    rw [hrun1] at work1 rel1
    have notNone : r1 ≠ none := by
      obtain ⟨_, _, _, _, hr, _⟩ := rel1
      simp only at hr
      rw [hr]
      cases result <;> simp [resultToLoop]
    obtain ⟨r1', rfl⟩ := Option.ne_none_iff_exists'.mp notNone
    have combined := LoopWork.seqStop (second := compileHOLExact context live second) work1
    refine ⟨e1, w1, ?_, by omega, ?_⟩
    · have sound := LoopWork.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound]
      exact combined
    · have sound := LoopWork.sound combined
      simp only [compileHOLExact] at sound ⊢
      rw [sound, evalCrepSemHOLProgExact_seq_holShape, run]
      simp only [reduceCtorEq, if_false]
      exact rel1
  | @iteBranch t condition yes no word branchWork guard branch ihBranch =>
    intro u context live ok rel covered
    simp only [crepLoopCovered, Bool.and_eq_true] at covered
    have okBranch : (evalCrepSemHOLProgExact t (if word ≠ 0 then yes else no)).1 ≠ some .error := by
      rw [evalCrepSemHOLProgExact_ite_holShape, guard] at ok; exact ok
    exact ite_loop_paid guard ok rel (fun u' rel' => ihBranch u' context live okBranch rel'
      (by by_cases hw : word = 0
          · rw [if_neg (by simp [hw])]; exact covered.2
          · rw [if_pos hw]; exact covered.1))
  | @iteInvalid t condition yes no invalid =>
    intro u context live ok rel covered
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_ite_holShape]
    split
    · rename_i w hw; exact absurd hw (invalid w)
    · rfl
  | @dec t name value body word bodyWork evaluated bodyRun ih =>
    intro u context live ok rel covered
    simp only [crepLoopCovered] at covered
    exact dec_loop_paid evaluated ok rel (fun u' c' l' ok' rel' => ih u' c' l' ok' rel' covered)
  | @decFailure t name value body failed =>
    intro u context live ok rel covered
    exfalso
    apply ok
    rw [evalCrepSemHOLProgExact_dec_holShape, failed]
  | @whileExit t condition body exit =>
    intro u context live ok rel covered
    cases hev : evalCrepSemHOLExp t condition with
    | none =>
      exfalso; apply ok; rw [evalCrepSemHOLProgExact_while_holShape, hev]
    | some v =>
      cases v with
      | word w =>
        have hw := exit w hev
        subst hw
        exact while_false_loop_paid hev rel
  | @whileTimeout t condition body word guard nonzero clock =>
    intro u context live ok rel covered
    exact while_timeout_loop_paid guard nonzero clock rel
  | @whileLoop t condition body word bodyWork result middle restWork guard nonzero clock one run
      again rest ihOne ihRest =>
    intro u context live ok rel covered
    have coveredBody : crepLoopCovered body = true := by
      simpa [crepLoopCovered] using covered
    have bodyOk := while_body_not_error guard nonzero clock run ok
    have restOk : (evalCrepSemHOLProgExact middle (.while condition body)).1 ≠ some .error := by
      have crepRun : evalCrepSemHOLProgExact t (.while condition body) =
          evalCrepSemHOLProgExact middle (.while condition body) := by
        rw [evalCrepSemHOLProgExact_while_holShape, guard]
        simp only [ne_eq, clock, if_false]
        rw [if_pos nonzero, run]
        rcases again with rfl | rfl <;> rfl
      rw [← crepRun]; exact ok
    exact while_loop_loop_paid guard nonzero clock run again rel
      (fun u' rel' => ihOne u' context live (by rw [run]; exact bodyOk) rel' coveredBody)
      (fun u' rel' => ihRest u' context live restOk rel' covered)
  | @whileStop t condition body word bodyWork result middle guard nonzero clock one run stop
      ihOne =>
    intro u context live ok rel covered
    have coveredBody : crepLoopCovered body = true := by
      simpa [crepLoopCovered] using covered
    have bodyOk := while_body_not_error guard nonzero clock run ok
    exact while_stop_loop_paid guard nonzero clock run stop ok rel
      (fun u' rel' => ihOne u' context live (by rw [run]; exact bodyOk) rel' coveredBody)
  | _ =>
    intro u context live ok rel covered
    first
      | exact leaf_loop_paid rfl ok rel
      | (simp [crepLoopCovered, crepLeafWork] at covered)

#print axioms crep_loop_executed_work
end InitECandidate.Runtime.FineCost
