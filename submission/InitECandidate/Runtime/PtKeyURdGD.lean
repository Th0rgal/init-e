import InitECandidate.Runtime.HashBody32
/-!
Byte-assembled reads for keys of arbitrary alignment.  The source `LD_LE32`/`LD_LE64` macros expand to an `or`
of `ld8` loads at `p + c₁ + …`, shifted into place.  `kuAddr`, `kuLe32` and `kuLe64` are those exact expression
shapes; each evaluates to a word as soon as every byte it reads lies in an addressable word (`memaddrs` of the
aligned word holding the byte).  No alignment of `p` is assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Source byte address `p + c₁ + …` (just `p` when there are no constants). -/
def kuAddr : List (BitVec 64) → ExpHOL 64
  | [] => .var .local (ofString "p")
  | cs => .op .add (.var .local (ofString "p") :: cs.map .const)

/-- Offset of `kuAddr cs` from `p`. -/
def kuOff (cs : List (BitVec 64)) : BitVec 64 := cs.foldr (· + ·) 0

/-- Source `LD_LE32` at `kuAddr base`. -/
def kuLe32 (base : List (BitVec 64)) : ExpHOL 64 :=
  .op .or [.loadByte (kuAddr base),
    .shift .lsl (.loadByte (kuAddr (base ++ [1]))) (.const 8),
    .shift .lsl (.loadByte (kuAddr (base ++ [2]))) (.const 16),
    .shift .lsl (.loadByte (kuAddr (base ++ [3]))) (.const 24)]

/-- Source `LD_LE64` at `kuAddr base`: low `LD_LE32`, high `LD_LE32` at `+4` shifted by 32. -/
def kuLe64 (base : List (BitVec 64)) : ExpHOL 64 :=
  .op .or [.loadByte (kuAddr base),
    .shift .lsl (.loadByte (kuAddr (base ++ [1]))) (.const 8),
    .shift .lsl (.loadByte (kuAddr (base ++ [2]))) (.const 16),
    .shift .lsl (.loadByte (kuAddr (base ++ [3]))) (.const 24),
    .shift .lsl (kuLe32 (base ++ [4])) (.const 32)]

theorem kuOff_append (base : List (BitVec 64)) (c : BitVec 64) : kuOff (base ++ [c]) = kuOff base + c := by
  induction base with
  | nil => simp [kuOff]
  | cons a rest ih =>
    simp only [kuOff, List.cons_append, List.foldr_cons] at ih ⊢
    rw [ih, BitVec.add_assoc]

section ev
variable {F : Type} (state : PanSemStateFiniteExact 64 F)

theorem eval_kuConsts (cs : List (BitVec 64)) :
    @evalListHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (cs.map .const) = some (cs.map fun c => .val (.word c)) := by
  induction cs with
  | nil => rfl
  | cons c rest ih => simp [evalListHOLExact, evalHOLExact, ih]

theorem eval_kuAddr (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer))) (cs : List (BitVec 64)) :
    @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (kuAddr cs) = some (.val (.word (pointer + kuOff cs))) := by
  cases cs with
  | nil => simpa [kuAddr, kuOff, evalHOLExact] using binding
  | cons c rest =>
    have hc := eval_kuConsts state (c :: rest)
    simp only [kuAddr]
    rw [evalHOLExact, evalListHOLExact]
    have hp : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
        (.var .local (ofString "p")) = some (.val (.word pointer)) := by simpa [evalHOLExact] using binding
    rw [hp, hc]
    simp [valueIsWord, valueWord, wordOpHOL, wordOp, kuOff, List.foldr_map]

theorem eval_kuByte (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer))) (cs : List (BitVec 64))
    (dom : state.memaddrs (panByteAlignHOL (pointer + kuOff cs))) :
    ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.loadByte (kuAddr cs)) =
        some (.val (.word v)) := by
  rw [evalHOLExact, eval_kuAddr state pointer binding cs]
  obtain ⟨w, cw⟩ : ∃ w : BitVec 64, state.memory (panByteAlignHOL (pointer + kuOff cs)) = .word w := by
    cases state.memory (panByteAlignHOL (pointer + kuOff cs)) with | word w => exact ⟨w, rfl⟩
  simp [panMemLoadByteHOL, cw, dom]

theorem eval_kuShift (e : ExpHOL 64) (o : Shift) (s v : BitVec 64) (hs : s.toNat < 64)
    (he : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address)) e =
      some (.val (.word v))) :
    ∃ v' : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.shift o e (.const s)) =
        some (.val (.word v')) := by
  rw [evalHOLExact, he]
  simp only [evalHOLExact]
  have : ¬ (s.toNat ≠ 0 ∧ 64 ≤ s.toNat) := by omega
  cases o <;> simp [wordShiftHOL, this]

theorem eval_kuWords (es : List (ExpHOL 64))
    (h : ∀ e ∈ es, ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) e = some (.val (.word v))) :
    ∃ ws : List (BitVec 64), @evalListHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) es = some (ws.map fun w => .val (.word w)) := by
  induction es with
  | nil => exact ⟨[], rfl⟩
  | cons e rest ih =>
    obtain ⟨v, hv⟩ := h e (by simp)
    obtain ⟨ws, hws⟩ := ih (fun x hx => h x (by simp [hx]))
    exact ⟨v :: ws, by simp [evalListHOLExact, hv, hws]⟩

theorem eval_kuOr (es : List (ExpHOL 64))
    (h : ∀ e ∈ es, ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) e = some (.val (.word v))) :
    ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (.op .or es) = some (.val (.word v)) := by
  obtain ⟨ws, hws⟩ := eval_kuWords state es h
  rw [evalHOLExact, hws]
  simp [valueIsWord, valueWord, wordOpHOL, wordOp]

/-- `LD_LE32` at `base` reads: every one of its four bytes lies in an addressable word. -/
theorem eval_kuLe32 (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer))) (base : List (BitVec 64))
    (dom : ∀ j : Nat, j < 4 → state.memaddrs (panByteAlignHOL (pointer + kuOff base + BitVec.ofNat 64 j))) :
    ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (kuLe32 base) = some (.val (.word v)) := by
  have b0 : state.memaddrs (panByteAlignHOL (pointer + kuOff base)) := by simpa using dom 0 (by omega)
  have bj : ∀ j : Nat, j < 4 → j ≠ 0 →
      state.memaddrs (panByteAlignHOL (pointer + kuOff (base ++ [BitVec.ofNat 64 j]))) := by
    intro j hj _; rw [kuOff_append, ← BitVec.add_assoc]; exact dom j hj
  obtain ⟨v0, e0⟩ := eval_kuByte state pointer binding base b0
  obtain ⟨v1, e1⟩ := eval_kuByte state pointer binding _ (bj 1 (by omega) (by omega))
  obtain ⟨v2, e2⟩ := eval_kuByte state pointer binding _ (bj 2 (by omega) (by omega))
  obtain ⟨v3, e3⟩ := eval_kuByte state pointer binding _ (bj 3 (by omega) (by omega))
  obtain ⟨s1, h1⟩ := eval_kuShift state _ .lsl 8 v1 (by decide) e1
  obtain ⟨s2, h2⟩ := eval_kuShift state _ .lsl 16 v2 (by decide) e2
  obtain ⟨s3, h3⟩ := eval_kuShift state _ .lsl 24 v3 (by decide) e3
  apply eval_kuOr
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact ⟨v0, e0⟩
  · exact ⟨s1, h1⟩
  · exact ⟨s2, h2⟩
  · exact ⟨s3, h3⟩

/-- `LD_LE64` at `base` reads: every one of its eight bytes lies in an addressable word. -/
theorem eval_kuLe64 (pointer : BitVec 64)
    (binding : state.locals.lookup (ofString "p") = some (.val (.word pointer))) (base : List (BitVec 64))
    (dom : ∀ j : Nat, j < 8 → state.memaddrs (panByteAlignHOL (pointer + kuOff base + BitVec.ofNat 64 j))) :
    ∃ v : BitVec 64, @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (kuLe64 base) = some (.val (.word v)) := by
  have b0 : state.memaddrs (panByteAlignHOL (pointer + kuOff base)) := by simpa using dom 0 (by omega)
  have bj : ∀ j : Nat, j < 4 → j ≠ 0 →
      state.memaddrs (panByteAlignHOL (pointer + kuOff (base ++ [BitVec.ofNat 64 j]))) := by
    intro j hj _; rw [kuOff_append, ← BitVec.add_assoc]; exact dom j (by omega)
  have hi : ∀ j : Nat, j < 4 →
      state.memaddrs (panByteAlignHOL (pointer + kuOff (base ++ [4]) + BitVec.ofNat 64 j)) := by
    intro j hj
    have := dom (4 + j) (by omega)
    rw [kuOff_append, ← BitVec.add_assoc, BitVec.add_assoc (pointer + kuOff base)]
    have e : (4 : BitVec 64) + BitVec.ofNat 64 j = BitVec.ofNat 64 (4 + j) := by
      apply BitVec.eq_of_toNat_eq; simp
    rw [e]; exact this
  obtain ⟨v0, e0⟩ := eval_kuByte state pointer binding base b0
  obtain ⟨v1, e1⟩ := eval_kuByte state pointer binding _ (bj 1 (by omega) (by omega))
  obtain ⟨v2, e2⟩ := eval_kuByte state pointer binding _ (bj 2 (by omega) (by omega))
  obtain ⟨v3, e3⟩ := eval_kuByte state pointer binding _ (bj 3 (by omega) (by omega))
  obtain ⟨v4, e4⟩ := eval_kuLe32 state pointer binding _ hi
  obtain ⟨s1, h1⟩ := eval_kuShift state _ .lsl 8 v1 (by decide) e1
  obtain ⟨s2, h2⟩ := eval_kuShift state _ .lsl 16 v2 (by decide) e2
  obtain ⟨s3, h3⟩ := eval_kuShift state _ .lsl 24 v3 (by decide) e3
  obtain ⟨s4, h4⟩ := eval_kuShift state _ .lsl 32 v4 (by decide) e4
  apply eval_kuOr
  intro e he
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact ⟨v0, e0⟩
  · exact ⟨s1, h1⟩
  · exact ⟨s2, h2⟩
  · exact ⟨s3, h3⟩
  · exact ⟨s4, h4⟩

end ev

#print axioms eval_kuAddr
#print axioms eval_kuLe32
#print axioms eval_kuLe64
end InitECandidate.Runtime
