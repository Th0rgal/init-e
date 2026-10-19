import InitECandidate.Runtime.WhileWordInvariant
import InitECandidate.Runtime.KeyNibbleStepWordFrame
import InitECandidate.Runtime.KeyToNibblesMainUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def NibbleWordInvariant {F : Type} (s : PanSemStateFiniteExact 64 F) (length out : BitVec 64) : Prop :=
  (∃ index : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word index)) ∧ index.toNat ≤ length.toNat) ∧
  s.locals.lookup (ofString "n") = some (.val (.word length)) ∧
  s.locals.lookup (ofString "out") = some (.val (.word out))

theorem evaluate_keyNibble_main_loop_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (length out watched : BitVec 64) (small : length.toNat + 4 < 2^64)
    (valid : NibbleWordInvariant s length out)
    (separate : ∀ offset : Nat, offset < 2 * length.toNat →
      watched ≠ panByteAlignHOL (out + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState s keyToNibblesMainLoop).2.memory watched = s.memory watched ∧
      ((evaluateHOLFiniteState s keyToNibblesMainLoop).1 = none →
        NibbleWordInvariant (evaluateHOLFiniteState s keyToNibblesMainLoop).2 length out) := by
  let condition : ExpHOL 64 := .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 4])
  have guard : ∀ current : PanSemStateFiniteExact 64 F, NibbleWordInvariant current length out →
      ∃ flag : BitVec 64, evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a)) condition =
        some (.val (.word flag)) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atN,atOut⟩
    refine ⟨if Compiler.Encoders.Asm.wordCmpHOL .notLower length (index + 4) then 1 else 0,?_⟩
    simp [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,atIndex,atN,wordOpHOL,wordOp,valueIsWord,valueWord]
  have step : ∀ current : PanSemStateFiniteExact 64 F, NibbleWordInvariant current length out → ∀ flag : BitVec 64,
      evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a)) condition =
        some (.val (.word flag)) → flag ≠ 0 →
      ∃ result post, evaluateHOLFiniteState (decClockHOLFinite current) keyToNibblesMainStep = (result,post) ∧
        post.clock = current.clock - 1 ∧ post.memory watched = current.memory watched ∧
        ((result = none ∧ NibbleWordInvariant post length out) ∨ result = some .error) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atN,atOut⟩ flag evaluated active
    have guardTrue : Compiler.Encoders.Asm.wordCmpHOL .notLower length (index + 4) = true := by
      by_contra no
      have flagEq : flag = if Compiler.Encoders.Asm.wordCmpHOL .notLower length (index + 4) then 1 else 0 := by
        simpa [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,atIndex,atN,wordOpHOL,wordOp,valueIsWord,valueWord] using evaluated.symm
      rw [Bool.eq_false_of_not_eq_true no] at flagEq
      exact active (by simpa using flagEq)
    have nextNat : (index + 4).toNat = index.toNat + 4 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 4 < 2^64; omega)]
      rfl
    have inside : index.toNat + 4 ≤ length.toNat := by
      have h : ¬length < index + 4 := by
        simpa [Compiler.Encoders.Asm.wordCmpHOL] using guardTrue
      change ¬length.toNat < (index + 4).toNat at h
      rw [nextNat] at h
      omega
    have disjoint : ∀ offset : Nat, offset < 8 →
        watched ≠ panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset)) := by
      intro offset insideOffset
      have address : 2 * index + BitVec.ofNat 64 offset = BitVec.ofNat 64 (2 * index.toNat + offset) := by
        simp [BitVec.ofNat_add,BitVec.ofNat_mul]
      rw [address]
      exact separate _ (by omega)
    have frame := evaluate_nibbleScopedWordFrame keyNibble_main_scopedWordFrame out index watched disjoint
      (decClockHOLFinite current) atOut atIndex
    obtain ⟨result,post,run,clock,locals,outcome⟩ := evaluate_keyToNibbles_main_step_frame (decClockHOLFinite current) index atIndex
    rw [run] at frame
    dsimp only at frame
    refine ⟨result,post,run,clock,frame,?_⟩
    rcases outcome with ⟨rfl,nextLocal⟩ | rfl
    · exact Or.inl ⟨rfl,⟨⟨index + 4,nextLocal,by rw [nextNat]; omega⟩,
        (locals _ (by decide)).trans atN,(locals _ (by decide)).trans atOut⟩⟩
    · exact Or.inr rfl
  have result := evaluate_while_word_invariant condition keyToNibblesMainStep
    (fun current => NibbleWordInvariant current length out) watched guard step s valid
  simpa only [source_keyToNibbles_main_loop,condition] using result

theorem evaluate_keyNibble_tail_loop_word_frame {F : Type} (s : PanSemStateFiniteExact 64 F)
    (length out watched : BitVec 64) (small : length.toNat + 4 < 2^64)
    (valid : NibbleWordInvariant s length out)
    (separate : ∀ offset : Nat, offset < 2 * length.toNat →
      watched ≠ panByteAlignHOL (out + BitVec.ofNat 64 offset)) :
    (evaluateHOLFiniteState s keyToNibblesTailLoop).2.memory watched = s.memory watched ∧
      ((evaluateHOLFiniteState s keyToNibblesTailLoop).1 = none →
        NibbleWordInvariant (evaluateHOLFiniteState s keyToNibblesTailLoop).2 length out) := by
  let condition : ExpHOL 64 := .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
  have guard : ∀ current : PanSemStateFiniteExact 64 F, NibbleWordInvariant current length out →
      ∃ flag : BitVec 64, evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a)) condition =
        some (.val (.word flag)) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atN,atOut⟩
    refine ⟨if Compiler.Encoders.Asm.wordCmpHOL .lower index length then 1 else 0,?_⟩
    simp [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,atIndex,atN,wordOpHOL,wordOp,valueIsWord,valueWord]
  have step : ∀ current : PanSemStateFiniteExact 64 F, NibbleWordInvariant current length out → ∀ flag : BitVec 64,
      evalHOLFinite current (h := fun a => Classical.propDecidable (current.memaddrs a)) condition =
        some (.val (.word flag)) → flag ≠ 0 →
      ∃ result post, evaluateHOLFiniteState (decClockHOLFinite current) keyToNibblesTailStep = (result,post) ∧
        post.clock = current.clock - 1 ∧ post.memory watched = current.memory watched ∧
        ((result = none ∧ NibbleWordInvariant post length out) ∨ result = some .error) := by
    rintro current ⟨⟨index,atIndex,bounded⟩,atN,atOut⟩ flag evaluated active
    have guardTrue : Compiler.Encoders.Asm.wordCmpHOL .lower index length = true := by
      by_contra no
      have flagEq : flag = if Compiler.Encoders.Asm.wordCmpHOL .lower index length then 1 else 0 := by
        simpa [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,atIndex,atN,wordOpHOL,wordOp,valueIsWord,valueWord] using evaluated.symm
      rw [Bool.eq_false_of_not_eq_true no] at flagEq
      exact active (by simpa using flagEq)
    have nextNat : (index + 1).toNat = index.toNat + 1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat + 1 < 2^64; omega)]
      rfl
    have inside : index.toNat + 1 ≤ length.toNat := by
      change decide (index.toNat < length.toNat) = true at guardTrue
      have h := of_decide_eq_true guardTrue
      omega
    have disjoint : ∀ offset : Nat, offset < 2 →
        watched ≠ panByteAlignHOL (out + (2 * index + BitVec.ofNat 64 offset)) := by
      intro offset insideOffset
      have address : 2 * index + BitVec.ofNat 64 offset = BitVec.ofNat 64 (2 * index.toNat + offset) := by
        simp [BitVec.ofNat_add,BitVec.ofNat_mul]
      rw [address]
      exact separate _ (by omega)
    have frame := evaluate_nibbleScopedWordFrame keyNibble_tail_scopedWordFrame out index watched disjoint
      (decClockHOLFinite current) atOut atIndex
    obtain ⟨result,post,run,clock,locals,outcome⟩ := evaluate_keyToNibbles_tail_step_frame (decClockHOLFinite current) index atIndex
    rw [run] at frame
    dsimp only at frame
    refine ⟨result,post,run,clock,frame,?_⟩
    rcases outcome with ⟨rfl,nextLocal⟩ | rfl
    · exact Or.inl ⟨rfl,⟨⟨index + 1,nextLocal,by rw [nextNat]; omega⟩,
        (locals _ (by decide)).trans atN,(locals _ (by decide)).trans atOut⟩⟩
    · exact Or.inr rfl
  have result := evaluate_while_word_invariant condition keyToNibblesTailStep
    (fun current => NibbleWordInvariant current length out) watched guard step s valid
  simpa only [source_keyToNibbles_tail_loop,condition] using result

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.evaluate_keyNibble_main_loop_word_frame
#print axioms InitECandidate.Runtime.evaluate_keyNibble_tail_loop_word_frame
