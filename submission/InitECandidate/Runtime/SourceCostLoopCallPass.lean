import InitECandidate.Runtime.SourceCostLoopCallInputs
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

private theorem call_comp_leaf (p : HolLoopProg 64) (cost : Nat) (labels : Spt Nat)
    (leaf : loopWorkLeafCost p = some cost) : (loopCallCompHOL labels p).1 = p := by
  cases p <;> simp only [loopWorkLeafCost, reduceCtorEq] at leaf
  all_goals try contradiction
  case assign name value => cases value <;> simp only [loopCallCompHOL]
  case arith operation => cases operation <;> simp only [loopCallCompHOL]
  all_goals first | rfl | simp only [loopCallCompHOL]

private theorem call_labels_empty {F : Type} (s : LoopSemStateFiniteExact 64 F) :
    labelsInHOL .ln s.locals := by intro n x found; simp [sptLookup] at found

private theorem call_cut_nonerror {F : Type} (live : NumSet)
    (output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F)
    (nonerror : (cutRes live output).1 ≠ some .error) : output.1 ≠ some .error := by
  intro bad
  rcases output with ⟨result, post⟩
  simp only [] at bad
  subst bad
  exact nonerror rfl

/-- The full actual known-label call pass never increases executed work.
Original semantic correctness supplies label-map preservation for reached
sequence suffixes; every transformed control rule uses its actual successor. -/
theorem LoopWork.call_comp {F : Type} {s : LoopSemStateFiniteExact 64 F}
    {p : HolLoopProg 64} {output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F}
    {w : Nat} (work : LoopWork s p output w) :
    ∀ labels : Spt Nat, labelsInHOL labels s.locals → output.1 ≠ some .error →
      ∃ w', LoopWork s (loopCallCompHOL labels p).1 output w' ∧ w' ≤ w := by
  induction work with
  | @atom s p output cost leaf run =>
    intro labels known nonerror
    rw [call_comp_leaf p cost labels leaf]
    exact ⟨cost, LoopWork.atom leaf run, Nat.le_refl _⟩
  | @mark s p output w inner ih =>
    intro labels known nonerror
    obtain ⟨w', marked, bound⟩ := ih labels known nonerror
    exact ⟨w', by simpa only [loopCallCompHOL] using LoopWork.mark marked, bound⟩
  | @seqNext s first second middle output a b one two ihOne ihTwo =>
    intro labels known nonerror
    rcases compiledFirst : loopCallCompHOL labels first with ⟨first', nextLabels⟩
    obtain ⟨a', one', boundOne⟩ := ihOne labels known (by simp)
    rw [compiledFirst] at one'
    have nextKnown := (loopCall_compile_correct first s none middle labels first' nextLabels
      ⟨one.sound, by simp, compiledFirst, known⟩).2
    obtain ⟨b', two', boundTwo⟩ := ihTwo nextLabels nextKnown nonerror
    refine ⟨a' + b', ?_, by omega⟩
    simpa only [loopCallCompHOL, compiledFirst] using LoopWork.seqNext one' two'
  | @seqStop s first second result post a one ih =>
    intro labels known nonerror
    obtain ⟨a', one', bound⟩ := ih labels known nonerror
    rcases compiledFirst : loopCallCompHOL labels first with ⟨first', nextLabels⟩
    rw [compiledFirst] at one'
    refine ⟨a', ?_, bound⟩
    simpa only [loopCallCompHOL, compiledFirst] using
      (LoopWork.seqStop (second := (loopCallCompHOL nextLabels second).1) one')
  | @iteBranch s operator register right yes no live x y output w lhs rhs branch ih =>
    intro labels known nonerror
    obtain ⟨w', branch', bound⟩ := ih labels known (call_cut_nonerror live output nonerror)
    have branch'' : LoopWork s
        (if Compiler.Encoders.Asm.wordCmpHOL operator x y then
          (loopCallCompHOL labels yes).1 else (loopCallCompHOL labels no).1) output w' := by
      split <;> simpa only [*, Bool.false_eq_true, ↓reduceIte] using branch'
    refine ⟨2 + w', ?_, by omega⟩
    simpa only [loopCallCompHOL] using LoopWork.iteBranch (live := live) lhs rhs branch''
  | iteInvalid invalid =>
    intro labels known nonerror
    exact False.elim (nonerror rfl)
  | @loopNext s liveIn body liveOut entry result middle output wb wr cut one again rest ihOne ihRest =>
    intro labels known nonerror
    have bodyOk : result ≠ some .error := by rcases again with rfl | rfl <;> simp
    obtain ⟨wb', body', bodyBound⟩ := ihOne .ln (call_labels_empty entry) bodyOk
    obtain ⟨wr', rest', restBound⟩ := ihRest .ln (call_labels_empty middle) nonerror
    simp only [loopCallCompHOL] at rest'
    refine ⟨3 + wb' + wr', ?_, by omega⟩
    simpa only [loopCallCompHOL] using LoopWork.loopNext cut body' again rest'
  | @loopBreak s liveIn body liveOut entry middle wb cut one ih =>
    intro labels known nonerror
    obtain ⟨wb', body', bound⟩ := ih .ln (call_labels_empty entry) (by simp)
    refine ⟨3 + wb', ?_, by omega⟩
    simpa only [loopCallCompHOL] using LoopWork.loopBreak (liveOut := liveOut) cut body'
  | @loopExit s liveIn body liveOut entry result middle wb cut one stop ih =>
    intro labels known nonerror
    have bodyOk : result ≠ some .error := by
      rintro rfl
      exact nonerror rfl
    obtain ⟨wb', body', bound⟩ := ih .ln (call_labels_empty entry) bodyOk
    refine ⟨3 + wb', ?_, by omega⟩
    simpa only [loopCallCompHOL] using LoopWork.loopExit (liveOut := liveOut) cut body' stop
  | loopCut stopped =>
    intro labels known nonerror
    exact ⟨3, by simpa only [loopCallCompHOL] using LoopWork.loopCut stopped, Nat.le_refl _⟩
  | callShort short run =>
    intro labels known nonerror
    exact loop_call_compiled_work (LoopWork.callShort short run) nonerror labels known
  | callTail args find noHandler clock body ih =>
    intro labels known nonerror
    exact loop_call_compiled_work (LoopWork.callTail args find noHandler clock body)
      nonerror labels known
  | callRet args find nodup cut body plain ih =>
    intro labels known nonerror
    exact loop_call_compiled_work (LoopWork.callRet args find nodup cut body plain)
      nonerror labels known
  | @callRetCont s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry returned post wb output wc args find nodup cut body lengths cont
      ihBody ihCont =>
    intro labels known nonerror
    exact loop_call_compiled_work
      (LoopWork.callRetCont (exceptionName := exceptionName) (liveOut := liveOut)
        (handlerProgram := handlerProgram) args find nodup cut body lengths cont)
      nonerror labels known
  | @callHandle s names live target arguments exceptionName handlerProgram continuation
      liveOut values env prog entry exn post wb output wh args find nodup cut body handle ihBody
      ihHandle =>
    intro labels known nonerror
    exact loop_call_compiled_work
      (LoopWork.callHandle (continuation := continuation) (liveOut := liveOut)
        args find nodup cut body handle) nonerror labels known

#print axioms LoopWork.call_comp
end InitECandidate.Runtime.FineCost
