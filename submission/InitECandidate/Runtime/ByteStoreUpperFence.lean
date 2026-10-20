import InitECandidate.Runtime.EncFenceBase
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A byte store strictly below a watched word preserves that word, in
every outcome, and a successful store exposes the actual domain check. -/
theorem r_stb_below {D : BitVec 64→Prop} {B : Bool} {A : GA→Prop} {w : BitVec 64}
 {Vn : MlS→Prop} {RR : ValueHOL 64→Mem→GA→Prop} {LP LQ : GA→Prop}
 (d v : ExpHOL 64)
 (hd : ∀{F : Type}(s : PanSemStateFiniteExact 64 F),A s.globals→LP s.locals→
  ∃a : BitVec 64,EV s d=some (.val (.word a)) ∧a.toNat<w.toNat ∧
   (D (panByteAlignHOL a)→LQ s.locals)) :
 AQGD D B A w Vn (fun L _ _=>LP L) (fun L _ _=>LQ L) RR (.storeByte d v) := by
 intro F s code dom aw sl G hG pre
 unfold GIs at hG;subst hG
 obtain ⟨a,ha,below,hq⟩:=hd s aw pre
 have separate : w≠panByteAlignHOL a := by
  intro eq
  have aligned:=align_toNat a
  have down:=Nat.div_mul_le_self a.toNat 8
  rw [←eq] at aligned
  omega
 obtain ⟨res,_,loc,glob,_,_,_⟩:=evaluate_storeByte_control_frame s d v
 refine ⟨evaluate_storeByte_memory_frame s d v a w ha separate,fun _=>by rw [glob];exact aw,
  fun e=>⟨by rw [loc];exact sl,_,by rw [glob];rfl,by
   rw [loc];exact hq (dom.2.1 ▸ storeByte_none_dom' s d v a ha e)⟩,?_,?_,?_⟩
 · intro value e;rcases res with h|h <;>rw [h] at e <;>cases e
 all_goals rcases res with h|h <;>rw [h] <;>simp

#print axioms r_stb_below
end InitECandidate.Runtime
