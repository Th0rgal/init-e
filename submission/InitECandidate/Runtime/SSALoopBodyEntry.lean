import InitECandidate.Runtime.SSALoopBackedgeExactCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopIteration

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact

/-! Public versions of the pinned private entry-cut derivations, for the
quantitative induction. They consume the actual refreshed strong relation;
they do not posit equal domains of arbitrary source/target locals. -/

theorem ssa_body_entry_locals {α : Type} (ssa : Spt Nat) (names : Spt Unit)
    (next : Nat) (source target : Spt α)
    (sourceDomain : sptDomain source = sptDomain names)
    (namesMapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (imagePresent : ∀ key, sptDomain names key → sptDomain target (optionLookup ssa key))
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa) (sptDomain names) source target)
    (bounded : ∀ key, sptDomain names key → key < next) :
    ssaLocalsRel next (sptInter ssa names) source target := by
  constructor
  · intro key register read
    rw [sptLookup_sptInterCases] at read
    cases original : sptLookup key ssa <;> cases named : sptLookup key names <;>
      simp [original,named] at read
    rename_i value marker
    have equal := read
    subst register
    have member : sptDomain names key := (sptMem_iff_lookup key names).mpr ⟨marker,named⟩
    simpa [optionLookup,original,sptMem] using imagePresent key member
  · intro key value read
    have member : sptDomain names key := by
      rw [← sourceDomain]
      exact (sptMem_iff_lookup key source).mpr ⟨value,read⟩
    obtain ⟨register,original⟩ := (sptMem_iff_lookup key ssa).mp (namesMapped key member)
    obtain ⟨marker,named⟩ := (sptMem_iff_lookup key names).mp member
    have mapped : sptLookup key (sptInter ssa names) = some register := by
      simp [sptLookup_sptInterCases,original,named]
    refine ⟨(sptMem_iff_lookup key _).mpr ⟨register,mapped⟩, ?_, fun _ => bounded key member⟩
    simpa [mapped,original,optionLookup] using strong key value ⟨member,read⟩

/-- Internal successful entry-cut derivation used by the full Loop helper.
These obligations occur inline in original7136-7154; no standalone HOL tag. -/
theorem ssa_loop_entry_cut {α : Type} (ssa : Spt Nat) (names : Spt Unit)
    (next : Nat) (source target sourceEnv : Spt α)
    (cut : wordSemCutEnv (names,.ln) source = some sourceEnv)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) source target)
    (injective : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup ssa x = optionLookup ssa y → x = y)
    (mapped : ∀ key, sptDomain names key → sptDomain ssa key)
    (bounded : ∀ key, sptDomain names key → key < next) :
    ∃ targetEnv,
      wordSemCutEnv (Flapjack.WordAlloc.applyNummapKey (optionLookup ssa) names,.ln)
        target = some targetEnv ∧
      sptDomain sourceEnv = sptDomain names ∧
      ssaLocalsRel next (sptInter ssa names) sourceEnv targetEnv := by
  have empty : ∀ key, ¬ sptDomain (Spt.ln : Spt Unit) key := by
    intro key
    simp [sptDomain]
  have jointInjective : ∀ x y, (sptDomain names x ∨ sptDomain (Spt.ln : Spt Unit) x) →
      (sptDomain names y ∨ sptDomain (Spt.ln : Spt Unit) y) →
      optionLookup ssa x = optionLookup ssa y → x = y := by
    intro x y hx hy equal
    exact injective x y (hx.resolve_right (empty x)) (hy.resolve_right (empty y)) equal
  have jointStrong : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (fun key => sptDomain names key ∨ sptDomain (Spt.ln : Spt Unit) key) source target := by
    intro key value h
    exact strong key value ⟨h.1.resolve_right (empty key),h.2⟩
  obtain ⟨targetEnv,targetCut,image,related,_,sourceDomain⟩ :=
    Flapjack.WordAlloc.cutEnvLemma names .ln source target sourceEnv (optionLookup ssa)
      ⟨jointInjective,cut,jointStrong⟩
  have domain : sptDomain sourceEnv = sptDomain names := by
    funext key
    exact (congrFun sourceDomain key).trans (propext (or_iff_left (empty key)))
  have cutRelated : Flapjack.WordAlloc.strongLocalsRel (optionLookup ssa)
      (sptDomain names) sourceEnv targetEnv := by
    intro key value h
    exact related key value ⟨Or.inl h.1,h.2⟩
  have present : ∀ key, sptDomain names key → sptDomain targetEnv (optionLookup ssa key) := by
    intro key h
    rw [image]
    exact ⟨key,by rw [domain]; exact h,rfl⟩
  refine ⟨targetEnv,?_,domain,ssa_body_entry_locals ssa names next sourceEnv targetEnv
    domain mapped present cutRelated bounded⟩
  simpa [Flapjack.WordAlloc.applyNummapsKey,Flapjack.WordAlloc.applyNummapKey,sptFromAList] using targetCut

/-- The actual source read in `ssaLocalsRel` supplies the strong relation
on any chosen domain. No equality of complete local domains is needed. -/
theorem ssa_locals_strong {α : Type} (next : Nat) (map : Spt Nat)
    (source target : Spt α) (domain : Nat → Prop)
    (related : ssaLocalsRel next map source target) :
    Flapjack.WordAlloc.strongLocalsRel (optionLookup map) domain source target := by
  intro key value inside
  cases found : sptLookup key map <;>
    simpa [optionLookup, found] using (related.2 key value inside.2).2.1

/-- Construct the actual target cut state and its SSA body-entry relation.
The body uses the intersected refreshed map, precisely as `ssaCcTrans` does. -/
theorem ssa_loop_body_entry {C F : Type} (refreshed : Spt Nat) (names : Spt Unit) (next : Nat)
    (source target : WordSemStateFiniteExact 64 C F) (sourceEnv : Spt (WordLocW 64))
    (cut : wordSemCutEnv (names, .ln) source.locals = some sourceEnv)
    (frame : Flapjack.WordAlloc.wordStateEqRel source target)
    (strong : Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed)
      (sptDomain names) source.locals target.locals)
    (injective : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup refreshed x = optionLookup refreshed y → x = y)
    (mapped : ∀ key, sptDomain names key → sptDomain refreshed key)
    (bounded : ∀ key, sptDomain names key → key < next) :
    ∃ targetEnv,
      cutState (names, .ln) source = some {source with locals := sourceEnv} ∧
      cutState (Flapjack.WordAlloc.applyNummapKey (optionLookup refreshed) names, .ln) target =
        some {target with locals := targetEnv} ∧
      Flapjack.WordAlloc.wordStateEqRel {source with locals := sourceEnv} {target with locals := targetEnv} ∧
      ssaLocalsRel next (sptInter refreshed names) sourceEnv targetEnv := by
  obtain ⟨targetEnv, targetCut, domain, related⟩ := ssa_loop_entry_cut refreshed names next
    source.locals target.locals sourceEnv cut strong injective mapped bounded
  refine ⟨targetEnv, ?_, ?_, ?_, related⟩
  · unfold cutState
    rw [cut]
  · unfold cutState
    rw [targetCut]
  · simpa only [Flapjack.WordAlloc.wordStateEqRel] using frame

#print axioms ssa_locals_strong
#print axioms ssa_body_entry_locals
#print axioms ssa_loop_entry_cut
#print axioms ssa_loop_body_entry
end InitECandidate.Runtime.FineCost
