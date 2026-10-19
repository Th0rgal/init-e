import InitECandidate.Runtime.CompactNibbleAfterAllocUniformBound
import InitECandidate.Runtime.CompactNibbleAllocate
import InitECandidate.Runtime.NodeNewBranchUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original allocation and compact-path continuation have a uniform bound,
including allocation rejection, without heap-space or byte-domain premises. -/
theorem runBounded_compact_nibble_allocate {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length c0 odd : BitVec 64)
    (small : (length - 1).toNat + 4 < 2^64)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "n") = some (.val (.word length)))
    (atByte : s.locals.lookup (ofString "c0") = some (.val (.word c0)))
    (atOdd : s.locals.lookup (ofString "odd") = some (.val (.word odd)))
    (code : s.code = originalRuntimeCode) (ticks : (length - 1).toNat / 4 + 6 ≤ s.clock) :
    RunBounded s compactNibbleAllocate ((length - 1).toNat / 4 + 6) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    HolFiniteMapExact.empty.update (ofString "n",.val (.word (2 * length)))
  let entry := callEntryStateHOLFinite s callee
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.panop .mul [.const 2,.var .local (ofString "n")]] = some [.val (.word (2 * length))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,panOpHOL,valueIsWord,valueWord]
  have lookup := pan_single_word_lookup s.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) (2 * length)
    (by rw [code]; exact originalRuntimeCode_allocation_lookup)
  have allocBound := evaluate_source_alloc_uniform_bounded entry code (by change 1 ≤ s.clock - 1; omega)
  have bounded : RunBounded entry (sourceFunctionBody Guest.guestFn_alloc) 1 :=
    ⟨allocBound.1,allocBound.2.1,allocBound.2.2.1⟩
  have reached : Reaches s compactNibbleAllocate
      (fun next => ∃ out : BitVec 64,
        next.locals = s.locals.update (ofString "out",.val (.word out)) ∧ next.code = originalRuntimeCode)
      2 compactNibbleAfterAlloc := by
    rw [source_compactNibble_allocate]
    apply bounded_decCall_reaches s (ofString "out") (ofString "alloc") .one .one _ _ _ _ callee 1 _
      args lookup (by omega) bounded
    intro value post run shapes
    obtain ⟨out,rfl⟩ := value_word_of_shape_one value ((shapeEqHOL_eq_true _ _).mp shapes.1)
    have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_alloc)
    rw [run] at metadata
    exact ⟨out,rfl,metadata.1.trans code⟩
  have whole : RunBounded s compactNibbleAllocate (2 + ((length - 1).toNat / 4 + 4)) :=
    RunBounded.ofReaches (by omega) reached (by
      intro next facts budget
      obtain ⟨out,locals,nextCode⟩ := facts
      have others : ∀ name, name ≠ ofString "out" → next.locals.lookup name = s.locals.lookup name := by
        intro name different
        rw [locals]
        simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
      have atOut : next.locals.lookup (ofString "out") = some (.val (.word out)) := by
        rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
      exact runBounded_compact_nibble_after_alloc next pointer length out c0 odd small
        ((others _ (by decide)).trans atPointer) ((others _ (by decide)).trans atLength)
        atOut ((others _ (by decide)).trans atByte) ((others _ (by decide)).trans atOdd) nextCode budget)
  simpa only [Nat.add_comm 2, Nat.add_assoc] using whole

#print axioms runBounded_compact_nibble_allocate
end InitECandidate.Runtime
