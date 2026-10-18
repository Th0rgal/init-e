import InitECandidate.Runtime.MemeqBody64BoundCap
import InitECandidate.Runtime.MemConstCallBound
import InitECandidate.Runtime.OriginalMemeqCode
import InitECandidate.Runtime.PanThreeValueLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem memeq_lookup_struct_none {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (x y z : ValueHOL 64)
    (bad : (∃ fs, x = .rStruct fs) ∨ (∃ n fs, x = .nStruct n fs) ∨ (∃ fs, y = .rStruct fs) ∨ (∃ n fs, y = .nStruct n fs)) :
    PanSemStateFiniteExact.lookupCodeHOLFinite state.code.lookup (ofString "memeq") [x,y,z] = none := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite
  split
  · rfl
  · rename_i found
    rw [code] at found
    rcases bad with ⟨fs,rfl⟩ | ⟨n,fs,rfl⟩ | ⟨fs,rfl⟩ | ⟨n,fs,rfl⟩ <;>
      simp [lookupCodeHOLExact,originalRuntimeCode_memeq_lookup,shapeOfHOLExact,shapeEqHOL] at found

/-- A declared memeq call with a literal size k (up to the heap cap) followed by a
bounded continuation, for ANY argument values and every outcome. -/
theorem memeq_decCall_const_progBounded (name : MlS) (a b : ExpHOL 64) (k : BitVec 64)
    (small : k.toNat ≤ 33806089496) {continuation : ProgHOL 64} {tailCost : Nat}
    (rest : ProgBounded continuation tailCost) :
    ProgBounded (.decCall name .one (ofString "memeq") [a,b,.const k] continuation) (4 * k.toNat + 1 + tailCost) := by
  intro F state code budget
  cases h : evalListHOLFinite state (h := fun x => Classical.propDecidable (state.memaddrs x)) [a,b,.const k] with
  | none =>
    rw [evaluateHOLFiniteState_decCall_args_none state name .one (ofString "memeq") [a,b,.const k] continuation h]; simp
  | some values =>
    obtain ⟨x,y,rfl⟩ := evalList_triple_const state a b k values h
    have struct : ∀ (bad : (∃ fs, x = .rStruct fs) ∨ (∃ n fs, x = .nStruct n fs) ∨ (∃ fs, y = .rStruct fs) ∨ (∃ n fs, y = .nStruct n fs)),
        let r := evaluateHOLFiniteState state (.decCall name .one (ofString "memeq") [a,b,.const k] continuation)
        state.clock ≤ r.2.clock + (4 * k.toNat + 1 + tailCost) ∧ r.2.clock ≤ state.clock ∧ r.1 ≠ some .timeOut := by
      intro bad
      rw [evaluateHOLFiniteState_decCall_lookup_none state name .one (ofString "memeq") [a,b,.const k] continuation _ h
        (memeq_lookup_struct_none state code x y _ bad)]
      simp
    cases x with
    | rStruct fs => exact struct (Or.inl ⟨fs,rfl⟩)
    | nStruct n fs => exact struct (Or.inr (Or.inl ⟨n,fs,rfl⟩))
    | val left =>
      cases y with
      | rStruct fs => exact struct (Or.inr (Or.inr (Or.inl ⟨fs,rfl⟩)))
      | nStruct n fs => exact struct (Or.inr (Or.inr (Or.inr ⟨n,fs,rfl⟩)))
      | val right =>
        let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
          ((HolFiniteMapExact.empty.update (ofString "a",.val left)).update (ofString "b",.val right)).update (ofString "n",.val (.word k))
        let entry := callEntryStateHOLFinite state callee
        have localN : entry.locals.lookup (ofString "n") = some (.val (.word k)) := by
          simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
        obtain ⟨result,post,body,cost,remaining,noTimeout⟩ := evaluate_memeq_body64_bounded_cap entry k localN small
          (by change 4 * k.toNat ≤ state.clock - 1; omega)
        have installed : state.code.lookup (ofString "memeq") =
            some ([(ofString "a",.one),(ofString "b",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_memeq,.one) := by
          rw [code]; exact originalRuntimeCode_memeq_lookup
        have lookup := pan_three_value_lookup state.code.lookup (ofString "memeq") (ofString "a") (ofString "b") (ofString "n")
          (sourceFunctionBody Guest.guestFn_memeq) left right (.word k) (by decide) (by decide) (by decide) installed
        have meta' := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_memeq)
        rw [body] at meta'
        exact evaluate_decCall_continuation_bounded state post name (ofString "memeq") .one .one [a,b,.const k]
          [.val left,.val right,.val (.word k)] (sourceFunctionBody Guest.guestFn_memeq) continuation callee result
          (4 * k.toNat + 1) tailCost h lookup (by omega) body remaining
          (by change state.clock - 1 ≤ post.clock + 4 * k.toNat at cost; omega) noTimeout
          (by
            intro value _
            apply rest
            · change post.code = originalRuntimeCode
              exact meta'.1.trans code
            · change tailCost ≤ post.clock
              change state.clock - 1 ≤ post.clock + 4 * k.toNat at cost
              omega)

#print axioms memeq_decCall_const_progBounded
end InitECandidate.Runtime
