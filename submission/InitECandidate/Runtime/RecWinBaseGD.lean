import InitECandidate.Runtime.EncodeTxFrameGD
import InitECandidate.Runtime.KeccakWindow
import InitECandidate.Runtime.HtabDelGD
/-!
Window rules for the `recover_sender_with_chain_id` frame: an external (FFI) call writes only the aligned words of its
array argument `[C, C + N)` (`aqgd_extCall`); `memcpy`, `memzero`, `keccak_absorb_block` as AQGD window specs.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An external call either errs (state unchanged), ends the run, or continues with locals and globals unchanged and
memory changed only in the aligned words of `[C, C + N)` where `C`, `N` are the array pointer and length. -/
theorem extCall_frame {F : Type} (s : PanSemStateFiniteExact 64 F) (f : MlS) (a b c d : ExpHOL 64) (C N w : BitVec 64)
    (hc : EV s c = some (.val (.word C))) (hd : EV s d = some (.val (.word N)))
    (out : ∀ j : Nat, j < N.toNat → w ≠ panByteAlignHOL (C + BitVec.ofNat 64 j)) :
    (evaluateHOLFiniteState s (.extCall f a b c d)).2.memory w = s.memory w ∧
    ((evaluateHOLFiniteState s (.extCall f a b c d)).1 = none ∧
        (evaluateHOLFiniteState s (.extCall f a b c d)).2.locals = s.locals ∧
        (evaluateHOLFiniteState s (.extCall f a b c d)).2.globals = s.globals ∨
      (evaluateHOLFiniteState s (.extCall f a b c d)).1 = some .error ∧
        (evaluateHOLFiniteState s (.extCall f a b c d)).2 = s ∨
      ∃ ev, (evaluateHOLFiniteState s (.extCall f a b c d)).1 = some (.finalFfi ev) ∧
        (evaluateHOLFiniteState s (.extCall f a b c d)).2.memory = s.memory ∧
        (evaluateHOLFiniteState s (.extCall f a b c d)).2.globals = s.globals) := by
  have ec : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word C)) := by
    rw [evalHOLFinite_eq_toExact]; exact hc
  have ed : evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) d = some (.val (.word N)) := by
    rw [evalHOLFinite_eq_toExact]; exact hd
  rw [evaluateHOLFiniteState_extCall_source]
  simp only [ec,ed]
  split
  · rename_i _ _ _ _ a1 l1 a2 l2 _ _ e3 e4
    simp only [Option.some.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq] at e3 e4
    subst e3 e4
    split
    · rename_i _ _ bytes1 bytes2 _ r2
      have len := readBytearrayWordHOL_length _ _ _ bytes2 r2
      split
      · exact ⟨rfl,Or.inr (Or.inr ⟨_,rfl,rfl,rfl⟩)⟩
      · rename_i newFfi newBytes hret
        have nl := callFFIHOL_ret_length _ _ _ _ _ _ hret
        exact ⟨@writeBytes_frame newBytes C s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be w
          (fun j hj => out j (by omega)),Or.inl ⟨rfl,rfl,rfl⟩⟩
    · exact ⟨rfl,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩
  · exact ⟨rfl,Or.inr (Or.inl ⟨rfl,rfl⟩)⟩

#print axioms extCall_frame

section ec
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}

/-- An external call writing into `[C, C + N)` avoiding the watched word. -/
theorem aqgd_extCall {LP LQ : GA → GA → Prop} (f : MlS) (a b c d : ExpHOL 64)
    (hd : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), A s.globals → LP s.locals s.globals →
      ∃ C N : BitVec 64, EV s c = some (.val (.word C)) ∧ EV s d = some (.val (.word N)) ∧
        (∀ j : Nat, j < N.toNat → w ≠ panByteAlignHOL (C + BitVec.ofNat 64 j)) ∧ LQ s.locals s.globals) :
    AQGD D B A w Vn (fun L _ G => LP L G) (fun L _ G => LQ L G) RR (.extCall f a b c d) := by
  intro F s code dom aw sl G hG pre
  unfold GIs at hG; subst hG
  obtain ⟨C,N,hc,hn,out,lq⟩ := hd s aw pre
  obtain ⟨m,h⟩ := extCall_frame s f a b c d C N w hc hn out
  refine ⟨m,?_,?_,?_,?_,?_⟩
  · intro hcont
    rcases h with ⟨_,_,glob⟩ | ⟨e,_⟩ | ⟨_,_,_,glob⟩
    · rw [glob]; exact aw
    · rw [e] at hcont; rcases hcont with h | h | h | ⟨_,h⟩ <;> cases h
    · rw [glob]; exact aw
  · intro e0
    rcases h with ⟨_,loc,glob⟩ | ⟨e,_⟩ | ⟨_,e,_,_⟩
    · refine ⟨by rw [loc]; exact sl,_,rfl,?_⟩
      rw [loc,glob]; exact lq
    · rw [e] at e0; cases e0
    · rw [e] at e0; cases e0
  · intro v e0
    rcases h with ⟨e,_,_⟩ | ⟨e,_⟩ | ⟨_,e,_,_⟩ <;> rw [e] at e0 <;> cases e0
  · rcases h with ⟨e,_,_⟩ | ⟨e,_⟩ | ⟨_,e,_,_⟩ <;> rw [e] <;> simp
  · rcases h with ⟨e,_,_⟩ | ⟨e,_⟩ | ⟨_,e,_,_⟩ <;> rw [e] <;> simp

#print axioms aqgd_extCall
end ec
section wn
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64}

theorem memcpy_wn (Dd S N : BitVec 64) (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin Dd N.toNat w) (M0 : Mem) (G0 : GA) :
    AQGD D B A w (fun _ => False)
      (fun L M G => (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        L.lookup (ofString "src") = some (.val (.word S)) ∧ L.lookup (ofString "n") = some (.val (.word N))) ∧
        M = M0 ∧ G = G0)
      (fun _ _ _ => True) (fun _ M' G' => G' = G0 ∧ ∀ x, ¬ MWin Dd N.toNat x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_memcpy) :=
  aqgd_of_window memcpy_body_globals_frame (by body_check Guest.guestFn_memcpy) (by body_check Guest.guestFn_memcpy)
    (MWin Dd N.toNat) (fun s _ ⟨hd,hs,hn⟩ x hx => memcpy_body_window s Dd S N x hd hs hn small hx) out M0 G0

theorem memzero_wn (Dd N : BitVec 64) (small : N.toNat + 32 < 2 ^ 64) (out : ¬ MWin Dd N.toNat w) (M0 : Mem) (G0 : GA) :
    AQGD D B A w (fun _ => False)
      (fun L M G => (L.lookup (ofString "dst") = some (.val (.word Dd)) ∧
        L.lookup (ofString "n") = some (.val (.word N))) ∧ M = M0 ∧ G = G0)
      (fun _ _ _ => True) (fun _ M' G' => G' = G0 ∧ ∀ x, ¬ MWin Dd N.toNat x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_memzero) :=
  aqgd_of_window memzero_body_globals_frame (by body_check Guest.guestFn_memzero) (by body_check Guest.guestFn_memzero)
    (MWin Dd N.toNat) (fun s _ ⟨hd,hn⟩ x hx => memzero_body_window s Dd N x hd hn small hx) out M0 G0

theorem absorb_wn (S : BitVec 64) (out : ¬ MWin S 200 w) (M0 : Mem) (G0 : GA) :
    AQGD D B A w (fun _ => False)
      (fun L M G => (L.lookup (ofString "stp") = some (.val (.word S)) ∧
        ∃ Bk : BitVec 64, L.lookup (ofString "blk") = some (.val (.word Bk))) ∧ M = M0 ∧ G = G0)
      (fun _ _ _ => True) (fun _ M' G' => G' = G0 ∧ ∀ x, ¬ MWin S 200 x → M' x = M0 x)
      (sourceFunctionBody Guest.guestFn_keccak_absorb_block) :=
  aqgd_of_window keccakAbsorb_body_globals_frame (by body_check Guest.guestFn_keccak_absorb_block)
    (by body_check Guest.guestFn_keccak_absorb_block) (MWin S 200)
    (fun s code ⟨hs,Bk,hb⟩ x hx => keccakAbsorb_body_window s S Bk x code hs hb hx) out M0 G0

#print axioms absorb_wn
end wn
end InitECandidate.Runtime
