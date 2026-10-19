import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
theorem value_three_words_of_checked_shape (value : ValueHOL 64)
    (checked : shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one,.one]) = true) :
    ∃ first second third : BitVec 64, value = .rStruct [.val (.word first),.val (.word second),.val (.word third)] := by
  have shape := (shapeEqHOL_eq_true _ _).mp checked
  cases value with
  | val atom => simp [shapeOfHOLExact] at shape
  | nStruct name fields => simp [shapeOfHOLExact] at shape
  | rStruct fields =>
    simp only [shapeOfHOLExact] at shape
    have fieldShapes : fields.map shapeOfHOLExact = [.one,.one,.one] := ShapeHOL.comb.inj shape
    have length : fields.length = 3 := by
      have same := congrArg List.length fieldShapes
      simpa using same
    cases fields with
    | nil => simp at length
    | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second rest =>
        cases rest with
        | nil => simp at length
        | cons third rest =>
          have empty : rest = [] := by
            cases rest with
            | nil => rfl
            | cons head tail => simp at length
          subst rest
          have shapes := List.cons.inj fieldShapes
          obtain ⟨word1,rfl⟩ := value_word_of_shape_one first shapes.1
          obtain ⟨word2,rfl⟩ := value_word_of_shape_one second (List.cons.inj shapes.2).1
          obtain ⟨word3,rfl⟩ := value_word_of_shape_one third (List.cons.inj (List.cons.inj shapes.2).2).1
          exact ⟨word1,word2,word3,rfl⟩

#print axioms value_three_words_of_checked_shape
end InitECandidate.Runtime
