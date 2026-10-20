import InitECandidate.Runtime.PtBalKeep2GD
import InitECandidate.Runtime.RecFrameGD
/-!
The process arena with the `bal_*` globals pinned (`JWB = JWSBUS ∧ BalG`). Within `process_transaction` after
`bal_index = index + 1` the `bal_*` globals are only read, so a triple over `JWSBUS` of a program passing `keepsG` for
every `bal_*` global (relative to `goodBal2`) holds over `JWB` (`aqgd_liftB`), a triple over `JWB` gives `BalG` as an
arena fact (`aqgd_balB`), and `JWB` is entered at a state where the `bal_*` globals hold some words (`aqgd_switchB`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The process arena with the `bal_*` globals at fixed values. -/
abbrev JWB (SP0 P0 FM : BitVec 64) (G0 : GA) (J C SKB Bo U Sc : BitVec 64) (BA IA IS KB Ix : BitVec 64) : GA → Prop :=
  fun g => JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc g ∧ BalG BA IA IS KB Ix g

section ab
variable {D : BitVec 64 → Prop} {B : Bool} {w : BitVec 64} {Vn : MlS → Prop} {RR : ValueHOL 64 → Mem → GA → Prop}
  {SP0 P0 FM : BitVec 64} {G0 : GA} {J C SKB Bo U Sc : BitVec 64} {BA IA IS KB Ix : BitVec 64}
  {P Q : GA → Mem → GA → Prop} {p : ProgHOL 64}

theorem balG_keep (bk : BalKeep2) (hk : balWatched.all (fun g => keepsG g goodBal2 p) = true) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) (bg : BalG BA IA IS KB Ix s.globals) :
    BalG BA IA IS KB Ix (evaluateHOLFiniteState s p).2.globals := by
  have keep : ∀ g ∈ balWatched, (evaluateHOLFiniteState s p).2.globals.lookup g = s.globals.lookup g := fun g hg =>
    evaluate_keepsG g goodBal2 (goodBal2_bodies bk g hg) p (List.all_eq_true.mp hk g hg) s code
  obtain ⟨b1,b2,b3,b4,b5⟩ := bg
  exact ⟨(keep _ (by simp [balWatched])).trans b1,(keep _ (by simp [balWatched])).trans b2,
    (keep _ (by simp [balWatched])).trans b3,(keep _ (by simp [balWatched])).trans b4,
    (keep _ (by simp [balWatched])).trans b5⟩

/-- Lifting a process-arena triple to `JWB` for a program keeping the `bal_*` globals. -/
theorem aqgd_liftB (bk : BalKeep2) (hk : balWatched.all (fun g => keepsG g goodBal2 p) = true)
    (h : AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn P Q RR p) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ix) w Vn P Q RR p :=
  aqgd_strengthen h (fun s code bg => balG_keep bk hk s code bg)

/-- `BalG` is an arena fact of `JWB`. -/
theorem aqgd_balB (h : AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ix) w Vn
      (fun L M G => P L M G ∧ BalG BA IA IS KB Ix G) Q RR p) :
    AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ix) w Vn P Q RR p :=
  fun F s code dom aw sl H hH pre => by
    unfold GIs at hH; subst hH
    exact h F s code dom aw sl _ rfl ⟨pre,aw.2⟩

/-- Entering `JWB` at a state where the `bal_*` globals hold some words. -/
theorem aqgd_switchB (h : ∀ BA IA IS KB Ix : BitVec 64, AQGD D B (JWB SP0 P0 FM G0 J C SKB Bo U Sc BA IA IS KB Ix) w Vn
      (fun L M G => P L M G ∧ BalG BA IA IS KB Ix G) Q RR p) :
    AQGD D B (JWSBUS SP0 P0 FM G0 J C SKB Bo U Sc) w Vn
      (fun L M G => P L M G ∧ ∃ BA IA IS KB Ix : BitVec 64, BalG BA IA IS KB Ix G) Q RR p := by
  intro F s code dom aw sl H hH ⟨pre,BA,IA,IS,KB,Ix,bg⟩
  unfold GIs at hH; subst hH
  obtain ⟨m,a,n,r,c,b⟩ := h BA IA IS KB Ix F s code dom ⟨aw,bg⟩ sl _ rfl ⟨pre,bg⟩
  exact ⟨m,fun cont => (a cont).1,n,r,c,b⟩

#print axioms aqgd_liftB
#print axioms aqgd_balB
#print axioms aqgd_switchB
end ab

theorem goodBal2_of_suf {f : MlS} (h : balSuf.contains f = true) : goodBal2 f = true := by
  unfold goodBal2 balExtra2; simp only [List.contains_append,Bool.or_eq_true]; exact Or.inr (Or.inr h)

theorem goodBal2_of_extra {f : MlS} (h : balExtra.contains f = true) : goodBal2 f = true := by
  unfold goodBal2 balExtra2; simp only [List.contains_append,Bool.or_eq_true]; exact Or.inr (Or.inl h)

theorem goodBal2_of_ga {f : MlS} (h : goodGA f = true) : goodBal2 f = true := by
  unfold goodBal2; simp only [Bool.or_eq_true]; exact Or.inl h

end InitECandidate.Runtime
