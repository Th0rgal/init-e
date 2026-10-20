import InitECandidate.Runtime.SourceCostLoopIf
import Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect.While
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

section LoopStep
/-! Flapjack helpers (no HOL declaration): one unfolding of loopSem's `Loop`
clause (`evaluate_def`, `loopSemScript.sml`) by the outcome of the entry
`cut_res` and of the body, as HOL's While case uses `Once evaluate_def`. -/

variable {width : Nat} [NeZero width] {F : Type}

theorem loopWhile_loop_step_cut_some {L L' : NumSet} {B : HolLoopProg width}
    {X Y : LoopSemStateFiniteExact width F} {r : LoopSemStateFiniteExact.LoopResultExact width}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (some r, Y)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = (some r, Y) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h => rw [hc] at h; simp at h
  next h => exact hc

theorem loopWhile_loop_step_none {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (none, s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.evaluate (.loop L B L') s2 := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

theorem loopWhile_loop_step_continue {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.continue 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.evaluate (.loop L B L') s2 := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

theorem loopWhile_loop_step_break {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F}
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some (.break 0), s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = LoopSemStateFiniteExact.cutRes L' (none, s2) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

theorem loopWhile_loop_step_exit {L L' : NumSet} {B : HolLoopProg width}
    {X X1 s2 : LoopSemStateFiniteExact width F} {r : LoopSemStateFiniteExact.LoopResultExact width}
    (hr0 : r ≠ .continue 0) (hr1 : r ≠ .break 0)
    (hc : LoopSemStateFiniteExact.cutRes L (none, X) = (none, X1))
    (hb : LoopSemStateFiniteExact.evaluate B X1 = (some r, s2)) :
    LoopSemStateFiniteExact.evaluate (.loop L B L') X = (LoopSemStateFiniteExact.exitLoop (some r), s2) := by
  rw [LoopSemStateFiniteExact.evaluate]
  split
  next X1' h =>
    rw [hc] at h
    simp only [Prod.mk.injEq, true_and] at h
    subst h
    split <;> rename_i h2 <;> rw [LoopSemStateFiniteExact.fix_clock_evaluate, hb] at h2 <;>
      simp_all [LoopSemStateFiniteExact.exitLoop]
  next h => exact absurd hc (h X1)

end LoopStep

section WhileHelpers
/-! Flapjack helpers (no HOL declaration) for HOL's While case: the
`locals_rel_def` / `domain_inter` / `lookup_inter` / `lookup_insert` steps, one
unfolding of the compiled loop body, and `exit_loop` against the result map. -/

variable {width : Nat} [NeZero width] {F : Type}

theorem loopWhile_locals_rel_inter (ctxt : CrepToLoopContextExact) (l : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl : Spt (WordLocW width))
    (h : crepToLoopLocalsRelExact ctxt l sl tl) :
    crepToLoopLocalsRelExact ctxt l sl (sptInter tl l) := by
  refine ⟨h.1, h.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · have hk' : (sptLookup k l).isSome := hk
    show (sptLookup k (sptInter tl l)).isSome
    rw [sptLookup_sptInter, if_pos hk']
    exact h.2.2.1 k hk
  · obtain ⟨n, hn1, hn2, hn3⟩ := h.2.2.2 vn val hval
    have hnl : (sptLookup n l).isSome := hn2
    refine ⟨n, hn1, hn2, ?_⟩
    show sptLookup n (sptInter tl l) = _
    rw [sptLookup_sptInter, if_pos hnl]
    exact hn3

/-- `locals_rel ctxt l` survives the compiled condition (whose output live set
    `nl` contains `l`) and the write of the fresh temporary `tmp > vmax`. -/
theorem loopWhile_locals_rel_insert_of (ctxt : CrepToLoopContextExact) (l nl : NumSet)
    (sl : HolFiniteMapExact Nat (HolWordLab width)) (tl tl' : Spt (WordLocW width))
    (hl : crepToLoopLocalsRelExact ctxt l sl tl) (h1l : crepToLoopLocalsRelExact ctxt nl sl tl')
    (hsub : ∀ k, sptDomain l k → sptDomain nl k) (tmp : Nat) (htmp : ctxt.vmax < tmp)
    (x : WordLocW width) :
    crepToLoopLocalsRelExact ctxt l sl (sptInsert tmp x tl') := by
  refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k (hsub k hk)))
  · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
    obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
    have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
    subst hnn
    have hle := h1l.2.1 vn n' hn1'
    refine ⟨n', hn1', hn2, ?_⟩
    rw [sptLookup_sptInsert, if_neg (by omega)]
    exact hn3'

theorem loopWhile_seq_continue_none {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F}
    (h : LoopSemStateFiniteExact.evaluate cC S = (none, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some (.continue 0), s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]
  simp only [LoopSemStateFiniteExact.evaluate]

theorem loopWhile_seq_continue_some {cC : HolLoopProg width}
    {S s' : LoopSemStateFiniteExact width F} {x : LoopSemStateFiniteExact.LoopResultExact width}
    (h : LoopSemStateFiniteExact.evaluate cC S = (some x, s')) :
    LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0)) S = (some x, s') := by
  rw [LoopSemStateFiniteExact.evaluate_seq, h]

/-- One run of the compiled While body `nested_seq (np ++ [Assign tmp le;
    If NotEqual tmp (Imm 0w) (Seq c (Continue 0)) (Break 0) l])`. -/
theorem loopWhile_while_body_eval (np : List (HolLoopProg width)) (le : HolLoopExp width)
    (tmp : Nat) (l : NumSet) (cC : HolLoopProg width) (Y st : LoopSemStateFiniteExact width F)
    (w : BitVec width) (h1 : LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np) Y = (none, st))
    (h1v : LoopSemStateFiniteExact.eval st le = some (.word w)) :
    LoopSemStateFiniteExact.evaluate
      (loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width)) (.seq cC (.continue 0)) (.break 0) l])) Y =
      if w = 0 then (some (.break 0), LoopSemStateFiniteExact.setVar tmp (.word w) st)
      else LoopSemStateFiniteExact.cutRes l
        (LoopSemStateFiniteExact.evaluate (.seq cC (.continue 0))
          (LoopSemStateFiniteExact.setVar tmp (.word w) st)) := by
  generalize (HolLoopProg.seq cC (.continue 0) : HolLoopProg width) = q
  rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ h1]
  simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
  simp only [LoopSemStateFiniteExact.evaluate, h1v]
  simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
    LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL]
  by_cases hw : w = 0
  · subst hw
    simp only [beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rfl
  · have hb : (w == 0) = false := by simpa using hw
    simp only [hb, Bool.not_false, if_true, hw, if_false]
    split <;> rename_i h <;> exact h.symm

theorem loopWhile_resultToLoop_exitLoop (r : CrepResultHOLExact width)
    (h0 : r ≠ .continue 0) (h1 : r ≠ .break 0) :
    LoopSemStateFiniteExact.exitLoop (resultToLoop (some r)) =
      resultToLoop (exitLoopCrepResult (some r)) := by
  cases r with
  | «continue» n => cases n with
    | zero => exact absurd rfl h0
    | succ n => rfl
  | «break» n => cases n with
    | zero => exact absurd rfl h1
    | succ n => rfl
  | _ => rfl

theorem loopWhile_localsResultRel_exitLoop (ctxt : CrepToLoopContextExact) (l : NumSet)
    (s : CrepSemHOLState width F) (tt : LoopSemStateFiniteExact width F)
    (r : CrepResultHOLExact width) (h : localsResultRel ctxt l (some r) s tt) :
    localsResultRel ctxt l (exitLoopCrepResult (some r)) s tt := by
  cases r <;> exact h

end WhileHelpers


#print axioms loopWhile_while_body_eval
end InitECandidate.Runtime.FineCost
