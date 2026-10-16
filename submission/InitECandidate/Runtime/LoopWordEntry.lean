import Flapjack.Pancake.LoopToWord.Proofs.StateRelImpSemantics
namespace InitECandidate.Runtime.LoopToWord
open Flapjack Flapjack.LoopToWord.CompileCorrect

/-- Concrete entry-run transfer at exactly the same initial fuel. It uses the
original full compiler relation and preserves its result-indexed postconditions. -/
theorem entry_same_clock {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (start fuel : Nat) (result : Option (LoopSemStateFiniteExact.LoopResultExact width))
    (post : LoopSemStateFiniteExact width F)
    (related : loopToWordStateRelHOLExact s t) (empty : s.locals = .ln)
    (entry : sptLookup 0 t.locals = some (.loc 1 0)) (dimension : goodDimindex width)
    (run : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none : HolLoopProg width)
      {s with clock := fuel} = (result,post)) (notError : result ≠ some .error) :
    ∃ final targetResult,
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
        {t with clock := fuel} = (targetResult,final) ∧
      final.ffi = post.ffi ∧
      resultCase (makeCtxtHOL 2 [] .ln) (.loc 1 0) {t with clock := fuel}
        result post targetResult final := by
  have locals : Flapjack.LoopToWord.localsRelHOL (makeCtxtHOL 2 [] .ln)
      ({s with clock := fuel} : LoopSemStateFiniteExact width F).locals
      ({t with clock := fuel} : WordSemStateFiniteExact width C F).locals := by
    change Flapjack.LoopToWord.localsRelHOL _ s.locals t.locals
    rw [empty]
    exact Flapjack.LoopToWord.localsRelHOLMkCtxtLn 2 [] _ ⟨by decide,by decide⟩
  obtain ⟨final,targetResult,evaluated,ffi,outcome⟩ := compileCorrect (C := C)
    (.call none (some start) [] none) {s with clock := fuel} result post
    {t with clock := fuel} (makeCtxtHOL 2 [] .ln) (.loc 1 0) (0,0)
    ⟨run,notError,loopToWordStateRelWithClockHOLExact s t fuel related,locals,entry,dimension,
      by simp [wordSemIsWordLoc],by intro x hx; simp [accVarsHOL,sptMem,sptDomain] at hx⟩
  have compiled : (Flapjack.LoopToWord.compHOL (makeCtxtHOL 2 [] .ln)
      (.call none (some start) [] none : HolLoopProg width) (0,0)).1 =
      .call none (some start) [0] none := by simp [Flapjack.LoopToWord.compHOL]
  rw [compiled] at evaluated
  exact ⟨final,targetResult,evaluated,ffi,outcome⟩

/-- Normal entry return keeps its values and the required top-level return location. -/
theorem entry_return_same_clock {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (start fuel : Nat) (values : List (WordLocW width)) (post : LoopSemStateFiniteExact width F)
    (related : loopToWordStateRelHOLExact s t) (empty : s.locals = .ln)
    (entry : sptLookup 0 t.locals = some (.loc 1 0)) (dimension : goodDimindex width)
    (run : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none : HolLoopProg width)
      {s with clock := fuel} = (some (.result values),post)) :
    ∃ final, WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {t with clock := fuel} = (some (.result (.loc 1 0) values),final) ∧ final.ffi = post.ffi := by
  obtain ⟨final,result,evaluated,ffi,outcome⟩ := entry_same_clock s t start fuel _ post
    related empty entry dimension run (by simp)
  obtain ⟨_,same,_,_⟩ := outcome
  rw [same] at evaluated
  exact ⟨final,evaluated,ffi⟩

/-- Final FFI events preserve their exact payload and FFI state at the same fuel. -/
theorem entry_ffi_same_clock {width : Nat} [NeZero width] {C F : Type}
    (s : LoopSemStateFiniteExact width F) (t : WordSemStateFiniteExact width C F)
    (start fuel : Nat) (event : HolFinalEvent) (post : LoopSemStateFiniteExact width F)
    (related : loopToWordStateRelHOLExact s t) (empty : s.locals = .ln)
    (entry : sptLookup 0 t.locals = some (.loc 1 0)) (dimension : goodDimindex width)
    (run : LoopSemStateFiniteExact.evaluate (.call none (some start) [] none : HolLoopProg width)
      {s with clock := fuel} = (some (.finalFfi event),post)) :
    ∃ final, WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {t with clock := fuel} = (some (.finalFfi event),final) ∧ final.ffi = post.ffi := by
  obtain ⟨final,result,evaluated,ffi,outcome⟩ := entry_same_clock s t start fuel _ post
    related empty entry dimension run (by simp)
  change result = some (.finalFfi event) at outcome
  rw [outcome] at evaluated
  exact ⟨final,evaluated,ffi⟩

#print axioms entry_same_clock
#print axioms entry_return_same_clock
#print axioms entry_ffi_same_clock
end InitECandidate.Runtime.LoopToWord
