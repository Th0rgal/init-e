import InitECandidate.Runtime.WordColourCostLoop
import InitECandidate.Runtime.WordColourCostReturn
import Flapjack.Compiler.Backend.WordAlloc.Proofs.WordAllocCorrect
import Flapjack.Compiler.Backend.WordToWord.FastCompile

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc Flapjack.RegAlloc
open Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordAlloc.Proofs (evenStartingLocals)
set_option maxHeartbeats 4000000

/-!
# Quantitative register allocation

`wordAlloc` (and the production `wordAllocWith`) is an oracle colouring when
`oracleColourOk` accepts it, else `applyColour (totalColour col)` for the
colouring computed by `selectRegAlloc`, else the unchanged program. Spilled
variables are colours at least `2 * k`; no Word instruction is inserted for
them, and their stack traffic is priced downstream by the name-independent
Word-to-Stack leaf prices. Every branch keeps executed work with coefficient one.
-/

/-- Quantitative `evaluate_apply_colour` on every program. -/
theorem colourCostGoal_all {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) :
    ∀ prog : WordLangProgHOL (BitVec 64), ColourCostGoal C F price prog
  | .seq c1 c2 => colourCost_seq price invariant c1 c2
      (colourCostGoal_all price invariant c1) (colourCostGoal_all price invariant c2)
  | .ite cmp r ri c1 c2 => colourCost_ite price invariant cmp r ri c1 c2
      (colourCostGoal_all price invariant c1) (colourCostGoal_all price invariant c2)
  | .mustTerminate body => colourCost_mustTerminate price invariant body
      (colourCostGoal_all price invariant body)
  | .loop names body exitNames => colourCost_loop price invariant names exitNames body
      (colourCostGoal_all price invariant body)
  | .call none dest args handler => colourCost_tail price invariant dest args handler
  | .call (some (n, (n1, n2), rh, l1, l2)) dest args none =>
      colourCost_returning price invariant n n1 n2 rh l1 l2 dest args none
        (colourCostGoal_all price invariant rh) (fun _ _ _ _ h => nomatch h)
  | .call (some (n, (n1, n2), rh, l1, l2)) dest args (some (v, hp, l1', l2')) =>
      colourCost_returning price invariant n n1 n2 rh l1 l2 dest args (some (v, hp, l1', l2'))
        (colourCostGoal_all price invariant rh)
        (fun _ _ _ _ h => by cases h; exact colourCostGoal_all price invariant hp)
  | .skip => colourCost_atomic price invariant _ rfl (applyColourGoal_all _)
  | .move pri moves => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.move pri moves))
  | .inst i => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.inst i))
  | .assign v e => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.assign v e))
  | .get v name => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.get v name))
  | .set name e => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.set name e))
  | .store e v => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.store e v))
  | .alloc n names => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.alloc n names))
  | .storeConsts a b c d ws =>
      colourCost_atomic price invariant _ rfl (applyColourGoal_all (.storeConsts a b c d ws))
  | .raise n => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.raise n))
  | .return n ms => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.return n ms))
  | .break k => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.break k))
  | .continue k => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.continue k))
  | .tick => colourCost_atomic price invariant _ rfl (applyColourGoal_all .tick)
  | .opCurrHeap b dst src =>
      colourCost_atomic price invariant _ rfl (applyColourGoal_all (.opCurrHeap b dst src))
  | .locValue r l1 => colourCost_atomic price invariant _ rfl (applyColourGoal_all (.locValue r l1))
  | .install ptr len dptr dlen names =>
      colourCost_atomic price invariant _ rfl (applyColourGoal_all (.install ptr len dptr dlen names))
  | .codeBufferWrite r1 r2 =>
      colourCost_atomic price invariant _ rfl (applyColourGoal_all (.codeBufferWrite r1 r2))
  | .dataBufferWrite r1 r2 =>
      colourCost_atomic price invariant _ rfl (applyColourGoal_all (.dataBufferWrite r1 r2))
  | .ffi fi p1 l1 p2 l2 names =>
      colourCost_atomic price invariant _ rfl (applyColourGoal_all (.ffi fi p1 l1 p2 l2 names))
  | .shareInst op v e =>
      colourCost_atomic price invariant _ rfl (applyColourGoal_all (.shareInst op v e))

/-- The allocator's whole-function contract with executed work: the HOL
`word_alloc_correct` conclusion and a coefficient-one cost bound, under one
source permutation. -/
def AllocCostPost {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (prog allocated : WordLangProgHOL (BitVec 64)) (st : WordSemStateFiniteExact 64 C F) : Prop :=
  ∃ permutation : Nat → Nat → Nat,
    let sourceState := {st with permute := permutation}
    let sourceRun := evaluate prog sourceState
    let targetRun := evaluate allocated st
    sourceRun.1 = some .error ∨
      sourceRun.1 = targetRun.1 ∧ wordStateEqRel sourceRun.2 targetRun.2 ∧
        (match sourceRun.1 with
         | none => True
         | some (.break _) => True
         | some (.continue _) => True
         | some _ => sourceRun.2.locals = targetRun.2.locals) ∧
        wordExecutionCost (fun p _ => price p) allocated st ≤
          wordExecutionCost (fun p _ => price p) prog sourceState

theorem allocCostPost_of_colour {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (f : Nat → Nat) (prog allocated : WordLangProgHOL (BitVec 64))
    (st : WordSemStateFiniteExact 64 C F) (shape : allocated = applyColour f prog)
    (post : ColourCostPost price f prog .ln [] st st) : AllocCostPost price prog allocated st := by
  subst shape
  obtain ⟨permutation, related⟩ := post
  refine ⟨permutation, ?_⟩
  dsimp only at related ⊢
  rcases related with bad | ⟨same, frame, locals, cost⟩
  · exact Or.inl bad
  · refine Or.inr ⟨same, frame, ?_, cost⟩
    generalize (evaluate prog {st with permute := permutation}) = sourceRun at locals ⊢
    rcases sourceRun with ⟨result, after⟩
    dsimp only at locals ⊢
    rcases result with _ | result
    · trivial
    · cases result <;> first | trivial | exact locals

theorem allocCostPost_self {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (prog : WordLangProgHOL (BitVec 64)) (st : WordSemStateFiniteExact 64 C F) :
    AllocCostPost price prog prog st := by
  refine ⟨st.permute, Or.inr ⟨rfl, wsrRefl _, ?_, Nat.le_refl _⟩⟩
  generalize (evaluate prog st) = run
  rcases run with ⟨result, after⟩
  rcases result with _ | result
  · trivial
  · cases result <;> first | trivial | rfl

/-- A colouring accepted by the clash-tree checker and fixing the physical
registers yields the quantitative allocator contract. -/
theorem allocCostPost_of_check {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (prog : WordLangProgHOL (BitVec 64))
    (st : WordSemStateFiniteExact 64 C F) (hesl : evenStartingLocals st.locals)
    (hwf : wfCutsets prog) (f : Nat → Nat) (livein flivein : NumSet)
    (hcc : checkClashTree f (getClashTree prog []) .ln .ln = some (livein, flivein))
    (hf : ∀ n, isPhyVar n = true → f n = n) :
    AllocCostPost price prog (applyColour f prog) st := by
  have hln : ∀ x, ¬ sptDomain (.ln : NumSet) x := fun x h => by
    simp [sptDomain, sptLookup] at h
  have hlnimg : sptDomain (.ln : NumSet) =
      (fun y => ∃ x, sptDomain (.ln : NumSet) x ∧ f x = y) := by
    funext y
    apply propext
    exact ⟨fun h => absurd h (hln y), fun ⟨x, hx, _⟩ => absurd hx (hln x)⟩
  have hco := (clashTreeColouringOk prog [] f .ln .ln livein flivein
    ⟨hwf, rfl, (fun _ h => by cases h), hlnimg,
      (fun a _ ha => absurd ha (hln a)), hcc⟩).2.2.1
  exact allocCostPost_of_colour price f prog _ st rfl
    (colourCostGoal_all price invariant prog st st f .ln [] ⟨hco, wsrRefl _,
      strongLocals_self f st.locals _ hesl hf⟩)

/-- Accepted oracle colourings (the candidate's supplied `colOracle`). -/
theorem allocCostPost_oracle {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (c : AsmConfigExact 64) (k : Nat)
    (prog coloured : WordLangProgHOL (BitVec 64)) (col_opt : Option (Spt Nat))
    (st : WordSemStateFiniteExact 64 C F) (hesl : evenStartingLocals st.locals)
    (hwf : wfCutsets prog)
    (hor : oracleColourOk k col_opt (getClashTree prog []) prog (getForced c prog []) = some coloured) :
    AllocCostPost price prog coloured st := by
  cases col_opt with
  | none => simp [oracleColourOk] at hor
  | some col =>
    simp only [oracleColourOk] at hor
    split at hor
    · next h1 =>
      split at hor
      · simp only [Option.some.injEq] at hor
        simp only [Bool.and_eq_true] at h1
        obtain ⟨hev, hcc⟩ := h1
        obtain ⟨⟨livein, flivein⟩, hcc⟩ := Option.isSome_iff_exists.mp hcc
        have hevc : ∀ x v, sptLookup x col = some v → isPhyVar x = true → 2 * v = x :=
          fun x v hl hp => by
            have hm := (sptMemToAList col x v).mpr hl
            have := List.all_eq_true.mp hev (x, v) hm
            simp only [hp, ↓reduceIte, beq_iff_eq] at this
            simp only [isPhyVar, decide_eq_true_eq] at hp
            omega
        rw [← hor]
        exact allocCostPost_of_check price invariant prog st hesl hwf (totalColour col)
          livein flivein hcc (totalColour_phys col hevc)
      · cases hor
    · cases hor

/-- Quantitative `word_alloc_correct`: every branch of the exact HOL allocator. -/
theorem wordAlloc_cost {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (fc : Nat) (c : AsmConfigExact 64) (alg : Nat)
    (prog : WordLangProgHOL (BitVec 64)) (k : Nat) (col_opt : Option (Spt Nat))
    (st : WordSemStateFiniteExact 64 C F) (hesl : evenStartingLocals st.locals)
    (hwf : wfCutsets prog) :
    AllocCostPost price prog (wordAlloc fc c alg k prog col_opt) st := by
  have hln : ∀ x, ¬ sptDomain (.ln : NumSet) x := fun x h => by
    simp [sptDomain, sptLookup] at h
  have hlnimg : ∀ (f : Nat → Nat), sptDomain (.ln : NumSet) =
      (fun y => ∃ x, sptDomain (.ln : NumSet) x ∧ f x = y) := fun f => by
    funext y
    apply propext
    exact ⟨fun h => absurd h (hln y), fun ⟨x, hx, _⟩ => absurd hx (hln x)⟩
  unfold wordAlloc
  simp only []
  cases hor : oracleColourOk k col_opt (getClashTree prog []) prog (getForced c prog []) with
  | some cp => exact allocCostPost_oracle price invariant c k prog cp col_opt st hesl hwf hor
  | none =>
    obtain ⟨hs, hgh⟩ : ∃ p, getHeuristics alg fc prog = p := ⟨_, rfl⟩
    obtain ⟨spcol, livein, flivein, hsel, hcc, hdom, hsup, _⟩ :=
      selectRegAllocCorrect alg hs.2 k hs.1 (getClashTree prog []) (getForced c prog [])
        (getStackOnly prog) (getForcedInGetClashTree prog [] c)
    have hinj : ∀ a b : Nat, (fun x => 2 * x) a = (fun x => 2 * x) b → a = b := fun a b h => by
      simp only at h; omega
    have hci := checkClashTreeInj (getClashTree prog []) (spDefault spcol) (fun x => 2 * x)
      .ln .ln .ln ⟨hinj, hlnimg _⟩
    rw [hcc] at hci
    obtain ⟨gout, hcc2, _⟩ := hci
    rw [← totalColourAlt] at hcc2
    have hphys : ∀ x v, sptLookup x spcol = some v → isPhyVar x = true → 2 * v = x :=
      fun x v hl hp => by
        have hd : sptDomain spcol x := by simp [sptDomain, hl]
        have hx := (hdom x (hsup x hd)).2
        rw [if_pos hp] at hx
        have : spDefault spcol x = v := by simp only [spDefault, hl]
        rw [this] at hx
        simp only [isPhyVar, decide_eq_true_eq] at hp
        omega
    rw [hgh]
    simp only [hsel]
    exact allocCostPost_of_check price invariant prog st hesl hwf (totalColour spcol) livein gout
      hcc2 (totalColour_phys spcol hphys)

/-- The production allocator entry point with the pinned graph allocator. -/
theorem wordAllocWith_cost {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (fc : Nat) (c : AsmConfigExact 64) (alg : Nat)
    (prog : WordLangProgHOL (BitVec 64)) (k : Nat) (col_opt : Option (Spt Nat))
    (st : WordSemStateFiniteExact 64 C F) (hesl : evenStartingLocals st.locals)
    (hwf : wfCutsets prog) :
    AllocCostPost price prog (WordToWord.wordAllocWith regAlloc fc c alg k prog col_opt) st := by
  rw [WordToWord.wordAllocWith_eq regAlloc rfl]
  exact wordAlloc_cost price invariant fc c alg prog k col_opt st hesl hwf

/-- Production allocation with ANY graph allocator whenever the supplied oracle
colouring is accepted, as for the candidate's certified `colOracle`. -/
theorem wordAllocWith_oracle_cost {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (ra : WordToWord.RegAllocFn) (fc : Nat)
    (c : AsmConfigExact 64) (alg : Nat) (prog coloured : WordLangProgHOL (BitVec 64)) (k : Nat)
    (col_opt : Option (Spt Nat)) (st : WordSemStateFiniteExact 64 C F)
    (hesl : evenStartingLocals st.locals) (hwf : wfCutsets prog)
    (hor : oracleColourOk k col_opt (getClashTree prog []) prog (getForced c prog []) = some coloured) :
    AllocCostPost price prog (WordToWord.wordAllocWith ra fc c alg k prog col_opt) st := by
  have shape : WordToWord.wordAllocWith ra fc c alg k prog col_opt = coloured := by
    unfold WordToWord.wordAllocWith
    simp only [hor]
  rw [shape]
  exact allocCostPost_oracle price invariant c k prog coloured col_opt st hesl hwf hor

/-- The pinned intermediate optimizer price satisfies the colouring premise. -/
theorem wordOptimizerPrice_colourInvariant {C F : Type} (s : WordSemStateFiniteExact 64 C F) :
    ColourPriceInvariant (fun p => wordOptimizerLocalPrice p s) := by
  intro f p
  exact Nat.le_of_eq (wordOptimizerLocalPrice_applyColour f p s)

#print axioms colourCostGoal_all
#print axioms allocCostPost_of_check
#print axioms allocCostPost_oracle
#print axioms wordAlloc_cost
#print axioms wordAllocWith_cost
#print axioms wordAllocWith_oracle_cost
#print axioms wordOptimizerPrice_colourInvariant
end InitECandidate.Runtime.FineCost
