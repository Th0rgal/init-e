import InitECandidate.Runtime.MemzeroCallBound
import InitECandidate.Runtime.MemcpyCallBound
import InitECandidate.Runtime.ProgBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evalList_pair_const {F : Type} (state : PanSemStateFiniteExact 64 F) (a : ExpHOL 64) (k : BitVec 64)
    (values : List (ValueHOL 64))
    (h : evalListHOLFinite state (h := fun x => Classical.propDecidable (state.memaddrs x)) [a,.const k] = some values) :
    ∃ x, values = [x,.val (.word k)] := by
  simp only [evalListHOLFinite,evalListHOLExact,evalHOLExact] at h
  split at h
  · rename_i x rest _ hrest
    simp [evalListHOLExact,evalHOLExact] at hrest
    subst hrest
    simp at h
    exact ⟨x,h.symm⟩
  · simp at h

/-- memzero with a literal size: every argument value and outcome stays within the
word-argument budget, since a structured destination fails the call lookup. -/
theorem memzero_const_progBounded (a : ExpHOL 64) (k : BitVec 64) (small : k.toNat ≤ 33806089496) :
    ProgBounded (.call (some (none,none)) (ofString "memzero") [a,.const k]) (k.toNat / 32 + k.toNat / 8 + 11) := by
  intro F state code budget
  cases h : evalListHOLFinite state (h := fun x => Classical.propDecidable (state.memaddrs x)) [a,.const k] with
  | none => rw [evaluateHOLFiniteState_call,h]; simp
  | some values =>
    obtain ⟨x,rfl⟩ := evalList_pair_const state a k values h
    cases x with
    | val w =>
      cases w with
      | word d => exact evaluate_memzero_call_bounded state _ d k h code small budget
    | rStruct fs =>
      have none : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup (ofString "memzero") [.rStruct fs,.val (.word k)] = none := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite
        split
        · rfl
        · rename_i found
          rw [code] at found
          simp [lookupCodeHOLExact,originalRuntimeCode_memzero_lookup,shapeOfHOLExact,shapeEqHOL] at found
      rw [evaluateHOLFiniteState_call,h]; dsimp only; rw [none]; simp
    | nStruct n fs =>
      have none : PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup (ofString "memzero") [.nStruct n fs,.val (.word k)] = none := by
        unfold PanSemStateFiniteExact.lookupCodeHOLFinite
        split
        · rfl
        · rename_i found
          rw [code] at found
          simp [lookupCodeHOLExact,originalRuntimeCode_memzero_lookup,shapeOfHOLExact,shapeEqHOL] at found
      rw [evaluateHOLFiniteState_call,h]; dsimp only; rw [none]; simp

#print axioms memzero_const_progBounded
theorem evalList_triple_const {F : Type} (state : PanSemStateFiniteExact 64 F) (a b : ExpHOL 64) (k : BitVec 64)
    (values : List (ValueHOL 64))
    (h : evalListHOLFinite state (h := fun x => Classical.propDecidable (state.memaddrs x)) [a,b,.const k] = some values) :
    ∃ x y, values = [x,y,.val (.word k)] := by
  simp only [evalListHOLFinite,evalListHOLExact,evalHOLExact] at h
  split at h
  · rename_i x rest _ hrest
    split at hrest
    · rename_i y rest2 _ hrest2
      simp [evalListHOLExact,evalHOLExact] at hrest2
      subst hrest2
      simp at hrest
      subst hrest
      simp at h
      exact ⟨x,y,h.symm⟩
    · simp at hrest
  · simp at h

theorem memcpy_lookup_struct_none {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (x y z : ValueHOL 64)
    (bad : (∃ fs, x = .rStruct fs) ∨ (∃ n fs, x = .nStruct n fs) ∨ (∃ fs, y = .rStruct fs) ∨ (∃ n fs, y = .nStruct n fs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup (ofString "memcpy") [x,y,z] = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rfl
  · rename_i found
    rw [code] at found
    rcases bad with ⟨fs,rfl⟩ | ⟨n,fs,rfl⟩ | ⟨fs,rfl⟩ | ⟨n,fs,rfl⟩ <;>
      simp [lookupCodeHOLExact,originalRuntimeCode_memcpy_lookup,shapeOfHOLExact,shapeEqHOL] at found

/-- memcpy with a literal size: every argument value and outcome stays within the
word-argument budget. -/
theorem memcpy_const_progBounded (a b : ExpHOL 64) (k : BitVec 64) (small : k.toNat ≤ 33806089496) :
    ProgBounded (.call (some (none,none)) (ofString "memcpy") [a,b,.const k]) (k.toNat / 32 + k.toNat / 8 + 11) := by
  intro F state code budget
  cases h : evalListHOLFinite state (h := fun x => Classical.propDecidable (state.memaddrs x)) [a,b,.const k] with
  | none => rw [evaluateHOLFiniteState_call,h]; simp
  | some values =>
    obtain ⟨x,y,rfl⟩ := evalList_triple_const state a b k values h
    have struct : ∀ (bad : (∃ fs, x = .rStruct fs) ∨ (∃ n fs, x = .nStruct n fs) ∨ (∃ fs, y = .rStruct fs) ∨ (∃ n fs, y = .nStruct n fs)),
        let r := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "memcpy") [a,b,.const k])
        state.clock ≤ r.2.clock + (k.toNat / 32 + k.toNat / 8 + 11) ∧ r.2.clock ≤ state.clock ∧ r.1 ≠ some .timeOut := by
      intro bad
      rw [evaluateHOLFiniteState_call,h]; dsimp only; rw [memcpy_lookup_struct_none state code x y _ bad]; simp
    cases x with
    | val w =>
      cases w with
      | word d =>
        cases y with
        | val w2 =>
          cases w2 with
          | word e => exact evaluate_memcpy_call_bounded state _ d e k h code small budget
        | rStruct fs => exact struct (Or.inr (Or.inr (Or.inl ⟨fs,rfl⟩)))
        | nStruct n fs => exact struct (Or.inr (Or.inr (Or.inr ⟨n,fs,rfl⟩)))
    | rStruct fs => exact struct (Or.inl ⟨fs,rfl⟩)
    | nStruct n fs => exact struct (Or.inr (Or.inl ⟨n,fs,rfl⟩))

#print axioms memcpy_const_progBounded
end InitECandidate.Runtime
