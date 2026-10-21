import InitECandidate.Runtime.SourceCostLoopLiveBaseG
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

variable {L : LeafPrice} {f : Nat}

/-- Shared live-local intersection geometry, independent of concrete states. -/
theorem live_mem_interG {α β : Type} (source : Spt α) (live : Spt β) (key : Nat) :
    sptMem key (sptInter source live) ↔ sptMem key source ∧ sptMem key live := by
  simp only [sptMem, sptDomain, sptLookup_sptInterCases]
  cases sptLookup key source <;> cases sptLookup key live <;> simp

theorem live_projection_lookupG {α : Type} {source target : Spt α} {live : NumSet}
    (input : sptSubspt (sptInter source live) target) {key : Nat} {value : α}
    (member : sptMem key live) (read : sptLookup key source = some value) :
    sptLookup key target = some value := by
  have present : sptMem key source := by simp [sptMem, sptDomain, read]
  have pair := input key ((live_mem_interG source live key).mpr ⟨present, member⟩)
  rw [pair.2, sptLookup_sptInter, if_pos (show (sptLookup key live).isSome = true from member)]
  exact read

/-- A proof for a wider input footprint supplies any smaller live footprint. -/
theorem live_projection_weakenG {α : Type} {source target : Spt α} {wide narrow : NumSet}
    (input : sptSubspt (sptInter source wide) target)
    (subset : ∀ key, sptMem key narrow → sptMem key wide) :
    sptSubspt (sptInter source narrow) target := by
  intro key member
  obtain ⟨present, needed⟩ := (live_mem_interG source narrow key).mp member
  have wideNeeded := subset key needed
  have pair := input key ((live_mem_interG source wide key).mpr ⟨present, wideNeeded⟩)
  refine ⟨pair.1, ?_⟩
  rw [pair.2, sptLookup_sptInter, sptLookup_sptInter,
    if_pos (show (sptLookup key wide).isSome = true from wideNeeded),
    if_pos (show (sptLookup key narrow).isSome = true from needed)]

/-- Shrinking an actual cut preserves its outcome and nonlocal state and
provides the needed body footprint. The original non-error guard implies the
source live-set domain; no extra successful-cut oracle is introduced. -/
theorem live_projection_cutG {F : Type} (s : LoopSemStateFiniteExact 64 F)
    (locals : Spt (WordLocW 64)) (wide narrow needed : NumSet)
    (input : sptSubspt (sptInter s.locals narrow) locals)
    (inside : ∀ key, sptMem key narrow → sptMem key wide)
    (needs : ∀ key, sptMem key needed → sptMem key wide → sptMem key narrow)
    (nonerror : (cutRes wide (none, s)).1 ≠ some .error) :
    ∃ targetLocals,
      cutRes narrow (none, { s with locals := locals }) =
        ((cutRes wide (none, s)).1, { (cutRes wide (none, s)).2 with locals := targetLocals }) ∧
      sptSubspt (sptInter (cutRes wide (none, s)).2.locals needed) targetLocals := by
  have sourceDomain : sptSubsetLive wide s.locals := by
    apply Classical.byContradiction
    intro missing
    apply nonerror
    simp only [cutRes, cutState_eq_none_of_not_subset wide s missing]
  have targetDomain : sptSubsetLive narrow locals := by
    intro key member
    exact (input key ((live_mem_interG s.locals narrow key).mpr
      ⟨sourceDomain key (inside key member), member⟩)).1
  simp only [cutRes, cutState_of_subset wide s sourceDomain,
    cutState_of_subset narrow { s with locals := locals } targetDomain]
  by_cases zero : s.clock = 0
  · simp only [zero, ↓reduceIte]
    refine ⟨.ln, rfl, ?_⟩
    simp [sptInter, sptSubspt, sptMem, sptDomain, sptLookup]
  · simp only [zero, ↓reduceIte]
    refine ⟨sptInter locals narrow, rfl, ?_⟩
    intro key member
    obtain ⟨inWide, inNeeded⟩ := (live_mem_interG (sptInter s.locals wide) needed key).mp member
    obtain ⟨inSource, inWide⟩ := (live_mem_interG s.locals wide key).mp inWide
    have inNarrow := needs key inNeeded inWide
    have pair := input key ((live_mem_interG s.locals narrow key).mpr ⟨inSource, inNarrow⟩)
    refine ⟨(live_mem_interG locals narrow key).mpr ⟨pair.1, inNarrow⟩, ?_⟩
    have eq : sptLookup key locals = sptLookup key s.locals := by
      simpa only [sptLookup_sptInter,
        if_pos (show (sptLookup key narrow).isSome = true from inNarrow)] using pair.2
    simpa only [decClock, sptLookup_sptInter,
      if_pos (show (sptLookup key narrow).isSome = true from inNarrow),
      if_pos (show (sptLookup key wide).isSome = true from inWide),
      if_pos (show (sptLookup key needed).isSome = true from inNeeded)] using eq

#print axioms live_projection_cutG
#print axioms live_projection_weakenG
#print axioms live_projection_lookupG
#print axioms live_mem_interG
end InitECandidate.Runtime.FineCost
