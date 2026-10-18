import InitECandidate.Runtime.TwoWordValueShape
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Checked u256 return shape supplies four actual word limbs. -/
theorem value_four_words_of_checked_shape (value : ValueHOL 64)
    (checked : shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one,.one,.one]) = true) :
    ∃ first second third fourth : BitVec 64,
      value = .rStruct [.val (.word first),.val (.word second),.val (.word third),.val (.word fourth)] := by
  have shape := (shapeEqHOL_eq_true _ _).mp checked
  cases value with
  | val atom => simp [shapeOfHOLExact] at shape
  | nStruct name fields => simp [shapeOfHOLExact] at shape
  | rStruct fields =>
    simp only [shapeOfHOLExact] at shape
    have fieldShapes : fields.map shapeOfHOLExact = [.one,.one,.one,.one] := ShapeHOL.comb.inj shape
    have length : fields.length = 4 := by
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
          cases rest with
          | nil => simp at length
          | cons fourth rest =>
            have empty : rest = [] := by
              cases rest with
              | nil => rfl
              | cons head tail => simp at length
            subst rest
            have s1 := List.cons.inj fieldShapes
            have s2 := List.cons.inj s1.2
            have s3 := List.cons.inj s2.2
            have s4 := List.cons.inj s3.2
            obtain ⟨w1,rfl⟩ := value_word_of_shape_one first s1.1
            obtain ⟨w2,rfl⟩ := value_word_of_shape_one second s2.1
            obtain ⟨w3,rfl⟩ := value_word_of_shape_one third s3.1
            obtain ⟨w4,rfl⟩ := value_word_of_shape_one fourth s4.1
            exact ⟨w1,w2,w3,w4,rfl⟩

#print axioms value_four_words_of_checked_shape
end InitECandidate.Runtime
