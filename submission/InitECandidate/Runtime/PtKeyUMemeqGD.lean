import InitECandidate.Runtime.PtKeyUMemeqStepGD
import InitECandidate.Runtime.PtKeyULoopQGD
import InitECandidate.Runtime.MemeqByte8Bound
/-!
The byte-comparison suffix of the source `memeq` (eight-byte loop, single-byte loop, `return 1`) on byte ranges whose
aligned cells are addressable: it returns `0` or `1`, keeps memory, domain, endianness, globals and code, and spends at
most `n` clocks.  No alignment of `a` or `b` is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

section mb
variable {F : Type} {M : BitVec 64 → HolWordLab 64} {D : BitVec 64 → Prop} {B : Bool} {G : HolFiniteMapExact MlS (ValueHOL 64)}
  {C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}

/-- Loop invariant of the byte suffix: operands and length bound, index in range, nonlocal state fixed. -/
def MbInv (a b n : BitVec 64) (M : BitVec 64 → HolWordLab 64) (D : BitVec 64 → Prop) (B : Bool) (G : HolFiniteMapExact MlS (ValueHOL 64)) (C : HolFiniteMapExact MlS
    (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (s : PanSemStateFiniteExact 64 F) : Prop :=
  s.locals.lookup (ofString "a") = some (.val (.word a)) ∧ s.locals.lookup (ofString "b") = some (.val (.word b)) ∧
  s.locals.lookup (ofString "n") = some (.val (.word n)) ∧
  (∃ i : BitVec 64, s.locals.lookup (ofString "i") = some (.val (.word i)) ∧ i.toNat ≤ n.toNat) ∧
  s.memory = M ∧ s.memaddrs = D ∧ s.be = B ∧ s.globals = G ∧ s.code = C

/-- Exit outcome of the byte suffix loops: `return 0` with the nonlocal state fixed. -/
def MbQ (M : BitVec 64 → HolWordLab 64) (D : BitVec 64 → Prop) (B : Bool) (G : HolFiniteMapExact MlS (ValueHOL 64)) (C : HolFiniteMapExact MlS
    (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) (r : PanSemResultExact 64) (s : PanSemStateFiniteExact 64 F) : Prop :=
  r = .returned (.val (.word 0)) ∧ s.memory = M ∧ s.memaddrs = D ∧ s.be = B ∧ s.globals = G ∧ s.code = C

theorem mbInv_dec {a b n : BitVec 64} {s : PanSemStateFiniteExact 64 F} (h : MbInv a b n M D B G C s) :
    MbInv a b n M D B G C (decClockHOLFinite s) := h

theorem mbInv_setI {a b n : BitVec 64} {s : PanSemStateFiniteExact 64 F} (h : MbInv a b n M D B G C s)
    (j : BitVec 64) (hj : j.toNat ≤ n.toNat) :
    MbInv a b n M D B G C (setVarHOLFinite (ofString "i") (.val (.word j)) s) := by
  obtain ⟨ha, hb, hn, _, hm, hd, he, hg, hc⟩ := h
  have ia : ofString "i" ≠ ofString "a" := by decide
  have ib : ofString "i" ≠ ofString "b" := by decide
  have inn : ofString "i" ≠ ofString "n" := by decide
  refine ⟨?_, ?_, ?_, ⟨j, ?_, hj⟩, hm, hd, he, hg, hc⟩ <;>
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, ia, ib, inn, ha, hb, hn]

theorem mb_cells {a b n i : BitVec 64} {s : PanSemStateFiniteExact 64 F}
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → s.memaddrs (panByteAlignHOL (a + x)) ∧ s.memaddrs (panByteAlignHOL (b + x)))
    (small : n.toNat ≤ 64) (k : Nat) (hk : i.toNat + k < n.toNat) (cs : List (BitVec 64)) (hcs : cs.foldr (· + ·) 0 = BitVec.ofNat 64 k) :
    s.memaddrs (panByteAlignHOL (a + (i + cs.foldr (· + ·) 0))) ∧ s.memaddrs (panByteAlignHOL (b + (i + cs.foldr (· + ·) 0))) := by
  rw [hcs]
  apply cells
  rw [BitVec.toNat_add_of_lt] <;> simp <;> omega

/-- One step of either byte loop on readable cells: advance by `k`, or return 0 from the unchanged state. -/
theorem mb_step {a b n : BitVec 64} {k : BitVec 64} {step : ProgHOL 64} (sup : ReadCheckAdvanceStep (ofString "i") k step)
    (s : PanSemStateFiniteExact 64 F) (i : BitVec 64) (hs : MbInv a b n M D B G C s)
    (hi : s.locals.lookup (ofString "i") = some (.val (.word i))) (hkn : i.toNat + k.toNat ≤ n.toNat)
    (readable : ∀ c ∈ rcChecks step, ∃ v : BitVec 64, @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) c = some (.val (.word v))) :
    ∃ post, s.clock ≤ post.clock + 0 ∧ post.clock ≤ s.clock ∧
      ((evaluateHOLFiniteState s step = (none, post) ∧ MbInv a b n M D B G C post ∧
          post.locals.lookup (ofString "i") = some (.val (.word (i + k)))) ∨
       (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ MbQ M D B G C result post ∧
          evaluateHOLFiniteState s step = (some result, post))) := by
  rcases evaluate_rcStep_readable sup s i hi readable with run | run
  · refine ⟨setVarHOLFinite (ofString "i") (.val (.word (i + k))) s, le_refl _, le_refl _, Or.inl ⟨run, mbInv_setI hs _ ?_, ?_⟩⟩
    · rw [BitVec.toNat_add_of_lt (by have := n.isLt; omega)]; omega
    · simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  · obtain ⟨_, _, _, _, hm, hd, he, hg, hc⟩ := hs
    exact ⟨emptyLocalsHOLFinite s, le_refl _, le_refl _, Or.inr ⟨_, by simp, by simp, by simp, ⟨rfl, hm, hd, he, hg, hc⟩, run⟩⟩

/-- Readable checks of one byte step at index `i` with `k` bytes ahead. -/
theorem mb_readable8 {a b n : BitVec 64} (s : PanSemStateFiniteExact 64 F) (i : BitVec 64)
    (hs : MbInv a b n M D B G C s) (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (a + x)) ∧ D (panByteAlignHOL (b + x)))
    (small : n.toNat ≤ 64) (h8 : i.toNat + 8 ≤ n.toNat) :
    ∀ c ∈ rcChecks memeqByte8Step, ∃ v : BitVec 64, @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) c = some (.val (.word v)) := by
  obtain ⟨ha, hb, _, _, _, hd, _⟩ := hs
  have cs : ∀ x : BitVec 64, x.toNat < n.toNat → s.memaddrs (panByteAlignHOL (a + x)) ∧ s.memaddrs (panByteAlignHOL (b + x)) := by
    rw [hd]; exact cells
  rw [rcChecks_memeqByte8]
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨da, db⟩ := mb_cells (i := i) cs small 0 (by omega) [] (by rfl)
    exact eval_mbCheck s a b i ha hb hi [] da db
  all_goals
    first
    | (obtain ⟨da, db⟩ := mb_cells (i := i) cs small 1 (by omega) [1] (by rfl); exact eval_mbCheck s a b i ha hb hi _ da db)
    | (obtain ⟨da, db⟩ := mb_cells (i := i) cs small 2 (by omega) [2] (by rfl); exact eval_mbCheck s a b i ha hb hi _ da db)
    | (obtain ⟨da, db⟩ := mb_cells (i := i) cs small 3 (by omega) [3] (by rfl); exact eval_mbCheck s a b i ha hb hi _ da db)
    | (obtain ⟨da, db⟩ := mb_cells (i := i) cs small 4 (by omega) [4] (by rfl); exact eval_mbCheck s a b i ha hb hi _ da db)
    | (obtain ⟨da, db⟩ := mb_cells (i := i) cs small 5 (by omega) [5] (by rfl); exact eval_mbCheck s a b i ha hb hi _ da db)
    | (obtain ⟨da, db⟩ := mb_cells (i := i) cs small 6 (by omega) [6] (by rfl); exact eval_mbCheck s a b i ha hb hi _ da db)
    | (obtain ⟨da, db⟩ := mb_cells (i := i) cs small 7 (by omega) [7] (by rfl); exact eval_mbCheck s a b i ha hb hi _ da db)

theorem mb_readable1 {a b n : BitVec 64} (s : PanSemStateFiniteExact 64 F) (i : BitVec 64)
    (hs : MbInv a b n M D B G C s) (hi : s.locals.lookup (ofString "i") = some (.val (.word i)))
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (a + x)) ∧ D (panByteAlignHOL (b + x)))
    (small : n.toNat ≤ 64) (h1 : i.toNat + 1 ≤ n.toNat) :
    ∀ c ∈ rcChecks memeqByte1Step, ∃ v : BitVec 64, @evalHOLExact 64 F _ s.toExact
      (fun address => Classical.propDecidable (s.memaddrs address)) c = some (.val (.word v)) := by
  obtain ⟨ha, hb, _, _, _, hd, _⟩ := hs
  have cs : ∀ x : BitVec 64, x.toNat < n.toNat → s.memaddrs (panByteAlignHOL (a + x)) ∧ s.memaddrs (panByteAlignHOL (b + x)) := by
    rw [hd]; exact cells
  rw [rcChecks_memeqByte1]
  intro c hc
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
  subst hc
  obtain ⟨da, db⟩ := mb_cells (i := i) cs small 0 (by omega) [] (by rfl)
  exact eval_mbCheck s a b i ha hb hi [] da db

theorem mb_loop8 {a b n : BitVec 64}
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (a + x)) ∧ D (panByteAlignHOL (b + x)))
    (small : n.toNat ≤ 64) (s : PanSemStateFiniteExact 64 F) (hs : MbInv a b n M D B G C s)
    (budget : memeqByte8Rank n s ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s memeqByte8Loop = (result, post) ∧
      s.clock ≤ post.clock + memeqByte8Rank n s ∧ post.clock ≤ s.clock ∧
      ((result = none ∧ MbInv a b n M D B G C post ∧ memeqByte8Rank n post = 0) ∨
       ∃ r, result = some r ∧ MbQ M D B G C r post) := by
  let condition : ExpHOL 64 := .cmp .notLower (.var .local (ofString "n")) (.op .add [.var .local (ofString "i"),.const 8])
  have guard : ∀ current : PanSemStateFiniteExact 64 F, MbInv a b n M D B G C current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition =
        some (.val (.word (if memeqByte8Rank n current = 0 then 0 else 1))) := by
    rintro current ⟨_, _, localN, ⟨i, localI, inside⟩, _⟩
    have rankEq : memeqByte8Rank n current = (n.toNat - i.toNat) / 8 := by simp [memeqByte8Rank, localI]
    have nextNat : (i + 8).toNat = i.toNat + 8 := by
      rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2 ^ 64; omega)]
      rfl
    by_cases done : memeqByte8Rank n current = 0
    · have outside : n < i + 8 := by
        apply BitVec.lt_def.mpr
        rw [nextNat]
        rw [rankEq] at done
        omega
      simp [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,localI,localN,wordOpHOL,wordOp,valueIsWord,valueWord,done,Compiler.Encoders.Asm.wordCmpHOL]
      exact outside
    · have below : i + 8 ≤ n := by
        apply BitVec.le_def.mpr
        rw [nextNat]
        rw [rankEq] at done
        omega
      simp [condition,evalHOLFinite,evalHOLExact,evalListHOLExact,localI,localN,wordOpHOL,wordOp,valueIsWord,valueWord,done,Compiler.Encoders.Asm.wordCmpHOL]
      exact below
  have step : ∀ current : PanSemStateFiniteExact 64 F, MbInv a b n M D B G C current → 0 < memeqByte8Rank n current →
      0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memeqByte8Step = (none,post) ∧ MbInv a b n M D B G C post ∧
            memeqByte8Rank n post < memeqByte8Rank n current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ MbQ M D B G C result post ∧
           evaluateHOLFiniteState current memeqByte8Step = (some result,post))) := by
    intro current hc positive _
    obtain ⟨i, localI, inside⟩ := hc.2.2.2.1
    have rankEq : memeqByte8Rank n current = (n.toNat - i.toNat) / 8 := by simp [memeqByte8Rank, localI]
    have below : i.toNat + 8 ≤ n.toNat := by rw [rankEq] at positive; omega
    obtain ⟨post, c1, c2, out⟩ := mb_step memeq_byte8_step_advances current i hc localI (by change i.toNat + 8 ≤ n.toNat; omega)
      (mb_readable8 current i hc localI cells small below)
    refine ⟨post, c1, c2, ?_⟩
    rcases out with ⟨run, inv, li⟩ | stop
    · have nextNat : (i + 8).toNat = i.toNat + 8 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 8 < 2 ^ 64; omega)]
        rfl
      have rankPost : memeqByte8Rank n post = (n.toNat - (i + 8).toNat) / 8 := by simp [memeqByte8Rank, li]
      exact Or.inl ⟨run, inv, by rw [rankPost, rankEq, nextNat]; omega⟩
    · exact Or.inr stop
  obtain ⟨result, post, run, cost, remaining, out⟩ := evaluate_ranked_loop_returnsQ condition memeqByte8Step
    (MbInv a b n M D B G C) (memeqByte8Rank n) 0 (MbQ M D B G C) guard (fun _ h => mbInv_dec h) (fun _ => rfl) step s hs
    (by simpa using budget)
  rw [source_memeq_byte8_loop]
  exact ⟨result, post, run, by simpa using cost, remaining, out⟩

theorem mb_loop1 {a b n : BitVec 64}
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (a + x)) ∧ D (panByteAlignHOL (b + x)))
    (small : n.toNat ≤ 64) (s : PanSemStateFiniteExact 64 F) (hs : MbInv a b n M D B G C s)
    (budget : memeqByteRank n s ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s memeqByte1Loop = (result, post) ∧
      s.clock ≤ post.clock + memeqByteRank n s ∧ post.clock ≤ s.clock ∧
      ((result = none ∧ MbInv a b n M D B G C post) ∨ ∃ r, result = some r ∧ MbQ M D B G C r post) := by
  let condition : ExpHOL 64 := .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
  have guard : ∀ current : PanSemStateFiniteExact 64 F, MbInv a b n M D B G C current →
      evalHOLFinite current (h := fun address => Classical.propDecidable (current.memaddrs address)) condition =
        some (.val (.word (if memeqByteRank n current = 0 then 0 else 1))) := by
    rintro current ⟨_, _, localN, ⟨i, localI, inside⟩, _⟩
    have rankEq : memeqByteRank n current = n.toNat - i.toNat := by simp [memeqByteRank, localI]
    by_cases done : i.toNat = n.toNat
    · have equal : i = n := BitVec.eq_of_toNat_eq done
      have zero : memeqByteRank n current = 0 := by rw [rankEq, done]; omega
      simp [condition,evalHOLFinite,evalHOLExact,localI,localN,equal,zero,Compiler.Encoders.Asm.wordCmpHOL]
    · have positive : memeqByteRank n current ≠ 0 := by rw [rankEq]; omega
      have below : i < n := BitVec.lt_def.mpr (by omega)
      simp [condition,evalHOLFinite,evalHOLExact,localI,localN,positive,Compiler.Encoders.Asm.wordCmpHOL,below]
  have step : ∀ current : PanSemStateFiniteExact 64 F, MbInv a b n M D B G C current → 0 < memeqByteRank n current →
      0 ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + 0 ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current memeqByte1Step = (none,post) ∧ MbInv a b n M D B G C post ∧
            memeqByteRank n post < memeqByteRank n current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ MbQ M D B G C result post ∧
           evaluateHOLFiniteState current memeqByte1Step = (some result,post))) := by
    intro current hc positive _
    obtain ⟨i, localI, inside⟩ := hc.2.2.2.1
    have rankEq : memeqByteRank n current = n.toNat - i.toNat := by simp [memeqByteRank, localI]
    have below : i.toNat + 1 ≤ n.toNat := by rw [rankEq] at positive; omega
    obtain ⟨post, c1, c2, out⟩ := mb_step memeq_byte1_step_advances current i hc localI (by change i.toNat + 1 ≤ n.toNat; omega)
      (mb_readable1 current i hc localI cells small below)
    refine ⟨post, c1, c2, ?_⟩
    rcases out with ⟨run, inv, li⟩ | stop
    · have nextNat : (i + 1).toNat = i.toNat + 1 := by
        rw [BitVec.toNat_add_of_lt (by change i.toNat + 1 < 2 ^ 64; omega)]
        rfl
      have rankPost : memeqByteRank n post = n.toNat - (i + 1).toNat := by simp [memeqByteRank, li]
      exact Or.inl ⟨run, inv, by rw [rankPost, rankEq, nextNat]; omega⟩
    · exact Or.inr stop
  obtain ⟨result, post, run, cost, remaining, out⟩ := evaluate_ranked_loop_returnsQ condition memeqByte1Step
    (MbInv a b n M D B G C) (memeqByteRank n) 0 (MbQ M D B G C) guard (fun _ h => mbInv_dec h) (fun _ => rfl) step s hs
    (by simpa using budget)
  rw [source_memeq_byte1_loop]
  refine ⟨result, post, run, by simpa using cost, remaining, ?_⟩
  rcases out with ⟨h1, h2, _⟩ | h
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr h

/-- The byte suffix returns `0` or `1`, keeps the nonlocal state, and spends at most `n` clocks. -/
theorem mb_suffix {a b n : BitVec 64}
    (cells : ∀ x : BitVec 64, x.toNat < n.toNat → D (panByteAlignHOL (a + x)) ∧ D (panByteAlignHOL (b + x)))
    (small : n.toNat ≤ 64) (s : PanSemStateFiniteExact 64 F) (hs : MbInv a b n M D B G C s)
    (budget : n.toNat ≤ s.clock) :
    ∃ v : BitVec 64, ∃ post, (v = 0 ∨ v = 1) ∧
      evaluateHOLFiniteState s memeqAfterAligned = (some (.returned (.val (.word v))), post) ∧
      s.clock ≤ post.clock + n.toNat ∧ post.clock ≤ s.clock ∧
      post.memory = M ∧ post.memaddrs = D ∧ post.be = B ∧ post.globals = G ∧ post.code = C := by
  obtain ⟨i, li, _⟩ := hs.2.2.2.1
  have r8 : memeqByte8Rank n s ≤ n.toNat := by simp [memeqByte8Rank, li]; omega
  obtain ⟨res8, p8, run8, cost8, rem8, out8⟩ := mb_loop8 cells small s hs (by omega)
  rw [source_memeq_byte_suffix, evaluateHOLFiniteState_seq_line780, run8]
  rcases out8 with ⟨rfl, inv8, _⟩ | ⟨r, rfl, hq, hm, hd, he, hg, hc⟩
  · obtain ⟨j, lj, _⟩ := inv8.2.2.2.1
    have r1 : memeqByteRank n p8 + memeqByte8Rank n s ≤ n.toNat := by
      simp [memeqByteRank, memeqByte8Rank, li, lj]
      have : memeqByte8Rank n p8 = 0 := by assumption
      simp [memeqByte8Rank, lj] at this
      omega
    obtain ⟨res1, p1, run1, cost1, rem1, out1⟩ := mb_loop1 cells small p8 inv8 (by omega)
    dsimp only
    rw [evaluateHOLFiniteState_seq_line780, run1]
    rcases out1 with ⟨rfl, inv1⟩ | ⟨r, rfl, hq, hm, hd, he, hg, hc⟩
    · obtain ⟨_, _, _, _, hm, hd, he, hg, hc⟩ := inv1
      refine ⟨1, emptyLocalsHOLFinite p1, Or.inr rfl, ?_, ?_, ?_, hm, hd, he, hg, hc⟩
      · simp [evaluateHOLFiniteState_return, evalHOLExact, shapeOfHOLExact, sizeOfShapeWithContextHOL]
      · change s.clock ≤ p1.clock + n.toNat; omega
      · change p1.clock ≤ s.clock; omega
    · subst hq
      exact ⟨0, p1, Or.inl rfl, rfl, by omega, by omega, hm, hd, he, hg, hc⟩
  · subst hq
    exact ⟨0, p8, Or.inl rfl, rfl, by omega, by omega, hm, hd, he, hg, hc⟩

end mb
#print axioms mb_step
#print axioms mb_readable8
#print axioms mb_readable1
#print axioms mb_loop8
#print axioms mb_loop1
#print axioms mb_suffix
end InitECandidate.Runtime
