import InitECandidate.Proofs.Op5.Separation
import Flapjack.Misc.SetSep

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Backend.StackRemove

/-- Extend both sides of the compiler's separated memory relation by an
independently owned arena. The complete old target domain excludes the arena,
so the existing frame cannot alias any of its addresses. -/
theorem memory_frame_extend {A V : Type} (m target : A → V)
    (domain targetDomain arena : A → Prop)
    (frame : ((A × V) → Prop) → Prop)
    (old : SetSep.star (memoryHOL m domain) frame
      (SetSep.fun2Set (target,targetDomain)))
    (disjoint : ∀ a, ¬ (arena a ∧ targetDomain a))
    (agree : ∀ a, arena a → m a = target a) :
    SetSep.star (memoryHOL m (fun a => domain a ∨ arena a)) frame
      (SetSep.fun2Set (target,fun a => targetDomain a ∨ arena a)) := by
  obtain ⟨left,right,part,hl,hr⟩ := old
  change left = SetSep.fun2Set (m,domain) at hl
  subst left
  have rightDomain : ∀ a v, right (a,v) → targetDomain a := by
    intro a v hv
    have h : SetSep.fun2Set (target,targetDomain) (a,v) := by
      rw [← part.1]
      exact Or.inr hv
    exact ((SetSep.fun2SetThm target targetDomain a v).mp h).2
  refine ⟨SetSep.fun2Set (m,fun a => domain a ∨ arena a),right,⟨?_,?_⟩,rfl,hr⟩
  · funext entry
    rcases entry with ⟨a,v⟩
    apply propext
    constructor
    · rintro (h | h)
      · obtain ⟨hv, hd | ha⟩ := (SetSep.fun2SetThm _ _ a v).mp h
        · have hOld : SetSep.fun2Set (target,targetDomain) (a,v) := by
            rw [← part.1]
            exact Or.inl ((SetSep.fun2SetThm _ _ a v).mpr ⟨hv,hd⟩)
          obtain ⟨ht,htd⟩ := (SetSep.fun2SetThm _ _ a v).mp hOld
          exact (SetSep.fun2SetThm _ _ a v).mpr ⟨ht,Or.inl htd⟩
        · exact (SetSep.fun2SetThm _ _ a v).mpr ⟨(agree a ha).symm.trans hv,Or.inr ha⟩
      · have hOld : SetSep.fun2Set (target,targetDomain) (a,v) := by
          rw [← part.1]
          exact Or.inr h
        obtain ⟨hv,hd⟩ := (SetSep.fun2SetThm _ _ a v).mp hOld
        exact (SetSep.fun2SetThm _ _ a v).mpr ⟨hv,Or.inl hd⟩
    · intro h
      obtain ⟨hv,hd | ha⟩ := (SetSep.fun2SetThm _ _ a v).mp h
      · have hOld := (SetSep.fun2SetThm target targetDomain a v).mpr ⟨hv,hd⟩
        rw [← part.1] at hOld
        rcases hOld with hm | hr
        · obtain ⟨hv,hd⟩ := (SetSep.fun2SetThm _ _ a v).mp hm
          exact Or.inl ((SetSep.fun2SetThm _ _ a v).mpr ⟨hv,Or.inl hd⟩)
        · exact Or.inr hr
      · exact Or.inl ((SetSep.fun2SetThm _ _ a v).mpr ⟨(agree a ha).trans hv,Or.inr ha⟩)
  · rintro ⟨a,v⟩ ⟨hleft,hright⟩
    obtain ⟨hv,hd | ha⟩ := (SetSep.fun2SetThm _ _ a v).mp hleft
    · exact part.2 (a,v) ⟨(SetSep.fun2SetThm _ _ a v).mpr ⟨hv,hd⟩,hright⟩
    · exact disjoint a ⟨ha,rightDomain a v hright⟩

/-- A separated scratch frame derives domain non-overlap. Both graphs use
one memory function, so shared address membership would duplicate a heap pair. -/
theorem memory_domains_disjoint {A V : Type} (m : A → V) (d e : A → Prop)
    (frame : ((A × V) → Prop) → Prop) (target : (A × V) → Prop)
    (heap : SetSep.star (memoryHOL m d) (SetSep.star (memoryHOL m e) frame) target) :
    ∀ a, ¬ (d a ∧ e a) := by
  obtain ⟨left,right,parts,hl,inside,rest,inner,he,_⟩ := heap
  change left = SetSep.fun2Set (m,d) at hl
  change inside = SetSep.fun2Set (m,e) at he
  intro a both
  have hd : left (a,m a) := by
    rw [hl]
    exact (SetSep.fun2SetThm m d a (m a)).mpr ⟨rfl,both.1⟩
  have ha : inside (a,m a) := by
    rw [he]
    exact (SetSep.fun2SetThm m e a (m a)).mpr ⟨rfl,both.2⟩
  have hr : right (a,m a) := by
    rw [← inner.1]
    exact Or.inl ha
  exact parts.2 (a,m a) ⟨hd,hr⟩

#print axioms memory_domains_disjoint
#print axioms memory_frame_extend
end InitE.Op5
