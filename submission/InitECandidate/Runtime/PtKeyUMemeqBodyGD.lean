import InitECandidate.Runtime.PtKeyUMemeqGD
import InitECandidate.Runtime.MemeqBodyWidths
import InitECandidate.Runtime.AlignedCellDomains
/-!
The complete source `memeq` body for 20/32/52-byte comparisons at any alignment of either operand, from the aligned
cells of the compared bytes alone: it returns `0` or `1`, keeps memory, globals, code, domain and endianness, and
spends at most `n` clocks.  The aligned branch reuses root's word fast paths with word cells derived from the byte
cells; otherwise the byte loops run (`mb_suffix`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

section mbody
variable {F : Type}

theorem eval_memeq_alignment_any (state : PanSemStateFiniteExact 64 F) (a b : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b))) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      memeqAlignmentCondition = some (.val (.word (if (a ||| b) &&& 7 = 0 then 1 else 0))) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .and [.op .or [.var .local (ofString "a"),.var .local (ofString "b")],.const 7]) =
        some (.val (.word ((a ||| b) &&& 7))) := by
    simp [evalHOLExact,evalListHOLExact,aLocal,bLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    change (a ||| (b ||| 0)) &&& ((7 : BitVec 64) &&& BitVec.allOnes 64) = (a ||| b) &&& 7
    have bz : b ||| (0 : BitVec 64) = b := by exact BitVec.or_zero
    rw [bz, BitVec.and_allOnes]
  unfold memeqAlignmentCondition
  rw [evalHOLExact, loaded]
  simp [evalHOLExact, Compiler.Encoders.Asm.wordCmpHOL]

theorem al_of_or_mask {a b : BitVec 64} (h : (a ||| b) &&& 7 = 0) : a.toNat % 8 = 0 ∧ b.toNat % 8 = 0 := by
  have ha : a &&& 7 = 0 := by
    ext i hi
    have := congrArg (fun x => x.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at this
    simp only [BitVec.getElem_and, BitVec.getElem_zero, ← BitVec.getLsbD_eq_getElem]
    cases h1 : a.getLsbD i <;> cases h2 : (7 : BitVec 64).getLsbD i <;> simp_all
  have hb : b &&& 7 = 0 := by
    ext i hi
    have := congrArg (fun x => x.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_zero] at this
    simp only [BitVec.getElem_and, BitVec.getElem_zero, ← BitVec.getLsbD_eq_getElem]
    cases h1 : b.getLsbD i <;> cases h2 : (7 : BitVec 64).getLsbD i <;> simp_all
  have m : ∀ x : BitVec 64, x &&& 7 = 0 → x.toNat % 8 = 0 := by
    intro x hx
    have := congrArg BitVec.toNat hx
    simp only [BitVec.toNat_and] at this
    change x.toNat &&& (2 ^ 3 - 1) = 0 at this
    rwa [Nat.and_two_pow_sub_one_eq_mod] at this
  exact ⟨m a ha, m b hb⟩

/-- Word cell at an aligned offset of an aligned operand, from its byte cells. -/
theorem mbWordCell (state : PanSemStateFiniteExact 64 F) (a n : BitVec 64) (al : a.toNat % 8 = 0)
    (fit : a.toNat + n.toNat < 2 ^ 64)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → state.memaddrs (panByteAlignHOL (a + x)))
    (off : Nat) (h1 : off < n.toNat) (h2 : off % 8 = 0) : state.memaddrs (a + BitVec.ofNat 64 off) := by
  have nat : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
  have c := cells (BitVec.ofNat 64 off) (by rw [nat]; exact h1)
  rwa [panByteAlign_eq_self_aligned _ (by rw [BitVec.toNat_add_of_lt (by rw [nat]; omega), nat]; omega)] at c

/-- Complete original `memeq` body for a supported width at any operand alignment. -/
theorem evaluate_source_memeqK (state : PanSemStateFiniteExact 64 F) (a b n : BitVec 64)
    (aLocal : state.locals.lookup (ofString "a") = some (.val (.word a)))
    (bLocal : state.locals.lookup (ofString "b") = some (.val (.word b)))
    (sizeLocal : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (sup : n = 20 ∨ n = 32 ∨ n = 52) (fitA : a.toNat + n.toNat < 2 ^ 64) (fitB : b.toNat + n.toNat < 2 ^ 64)
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat →
      state.memaddrs (panByteAlignHOL (a + x)) ∧ state.memaddrs (panByteAlignHOL (b + x)))
    (budget : n.toNat ≤ state.clock) :
    ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) = (some (.returned (.val (.word value))),post) ∧
      post.clock ≤ state.clock ∧ state.clock ≤ post.clock + n.toNat ∧ post.memory = state.memory ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  have cond := eval_memeq_alignment_any (setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state) a b
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "a" by decide] using aLocal)
    (by simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "b" by decide] using bLocal)
  by_cases al : (a ||| b) &&& 7 = 0
  · obtain ⟨aA, bA⟩ := al_of_or_mask al
    have wc : ∀ off ∈ ([0,8,16,24,32,40] : List Nat), off < n.toNat →
        state.memaddrs (a + BitVec.ofNat 64 off) ∧ state.memaddrs (b + BitVec.ofNat 64 off) := by
      intro off hm hl
      have h8 : off % 8 = 0 := by simp at hm; omega
      exact ⟨mbWordCell state a n aA fitA (fun x hx => (cells x hx).1) off hl h8,
        mbWordCell state b n bA fitB (fun x hx => (cells x hx).2) off hl h8⟩
    have bc : ∀ off : Nat, off < n.toNat →
        state.memaddrs (panByteAlignHOL (a + BitVec.ofNat 64 off)) ∧ state.memaddrs (panByteAlignHOL (b + BitVec.ofNat 64 off)) :=
      fun off hl => cells _ (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hl)
    have fin : ∀ v post, ((v : BitVec 64) = 0 ∨ v = 1) →
        evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) = (some (.returned (.val (.word v))),post) →
        post.clock = state.clock → post.memory = state.memory → post.globals = state.globals →
        post.code = state.code → post.memaddrs = state.memaddrs → post.be = state.be →
        ∃ value : BitVec 64, ∃ post, (value = 0 ∨ value = 1) ∧
          evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_memeq) = (some (.returned (.val (.word value))),post) ∧
          post.clock ≤ state.clock ∧ state.clock ≤ post.clock + n.toNat ∧ post.memory = state.memory ∧
          post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
      intro v post h0 h1 h2 h3 h4 h5 h6 h7
      exact ⟨v, post, h0, h1, by omega, by omega, h3, h4, h5, h6, h7⟩
    rcases sup with rfl | rfl | rfl
    · obtain ⟨v, post, h0, h1, h2, h3, h4, h5, h6, h7⟩ := evaluate_source_memeq20 state a b aLocal bLocal sizeLocal aA bA
        (fun off hm => wc off (by simp at hm ⊢; omega) (by simp at hm; change off < 20; omega))
        (fun off hm => bc off (by simp at hm; change off < 20; omega))
      exact fin v post h0 h1 h2 h3 h4 h5 h6 h7
    · obtain ⟨v, post, h0, h1, h2, h3, h4, h5, h6, h7⟩ := evaluate_source_memeq32 state a b aLocal bLocal sizeLocal aA bA
        (fun off hm => wc off (by simp at hm ⊢; omega) (by simp at hm; change off < 32; omega))
      exact fin v post h0 h1 h2 h3 h4 h5 h6 h7
    · obtain ⟨v, post, h0, h1, h2, h3, h4, h5, h6, h7⟩ := evaluate_source_memeq52 state a b aLocal bLocal sizeLocal aA bA
        (fun off hm => wc off (by simp at hm ⊢; omega) (by simp at hm; change off < 52; omega))
        (fun off hm => bc off (by simp at hm; change off < 52; omega))
      exact fin v post h0 h1 h2 h3 h4 h5 h6 h7
  · let entered := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
    have small : n.toNat ≤ 64 := by rcases sup with rfl | rfl | rfl <;> decide
    have inv : MbInv a b n state.memory state.memaddrs state.be state.globals state.code entered := by
      have na : ofString "i" ≠ ofString "a" := by decide
      have nb : ofString "i" ≠ ofString "b" := by decide
      have nn : ofString "i" ≠ ofString "n" := by decide
      refine ⟨?_, ?_, ?_, ⟨0, ?_, by simp⟩, rfl, rfl, rfl, rfl, rfl⟩ <;>
        simp [entered, setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, na, nb, nn, aLocal, bLocal, sizeLocal]
    obtain ⟨v, post, hv, run, c1, c2, hm, hd, he, hg, hc⟩ := mb_suffix (fun x hx => cells x hx) small entered inv budget
    have selected : evaluateHOLFiniteState entered
        (.seq (.ite memeqAlignmentCondition memeqAlignedBody .skip) memeqAfterAligned) =
        (some (.returned (.val (.word v))), post) := by
      rw [evaluateHOLFiniteState_seq_line780, evaluateHOLFiniteState_ite, cond]
      simp only [al, if_false, if_true, evaluateHOLFiniteState_skip]
      exact run
    rw [source_memeq_scoped_body, evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact]
    have shapeOk : shapeEqHOL .one (shapeOfHOLExact (.val (.word (0 : BitVec 64)))) = true := by
      simp [shapeEqHOL, shapeOfHOLExact]
    rw [if_pos shapeOk, selected]
    exact ⟨v, _, hv, rfl, c2, c1, hm, hg, hc, hd, he⟩

end mbody
#print axioms evaluate_source_memeqK
end InitECandidate.Runtime
