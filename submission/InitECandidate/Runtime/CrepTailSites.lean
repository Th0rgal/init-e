import InitECandidate.Runtime.SourceCostLoopWorkWs
import InitECandidate.Runtime.TailSiteTable
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Certified per-callee tail-call surcharge tables: `wsTail (some l)` is at
most `tailSitesL l`, a 16-label table read off the WordSimp site tables. A
source call charge can pay `tailSitesL` of its callee label. -/

/-- Per-label maxima of the kind-1 (tail) entries of `wsT1`. -/
def tail1 : List (Nat × Nat) :=
  [(117, 4), (128, 1), (131, 3), (135, 4), (174, 1), (176, 1), (211, 4), (212, 4), (214, 4), (221, 4),
   (222, 4), (298, 1), (299, 1), (308, 1), (369, 2), (372, 2)]

/-- Per-label maxima of the kind-1 (tail) entries of `wsT2`. -/
def tail2 : List (Nat × Nat) := [(117, 4), (128, 1), (131, 6), (298, 1), (299, 1)]

def tailLook (L : List (Nat × Nat)) (l : Nat) : Nat := (L.lookup l).getD 0

/-- The certified tail surcharge of callee label `l`. -/
def tailSitesL (l : Nat) : Nat := 24 * (tailLook tail2 l + tailLook tail1 l)

/-- Every tail entry of `T` is within the table at its destination label. -/
def tailOk (T : SiteTable) (L : List (Nat × Nat)) : Bool :=
  T.all (fun e => e.1.1 != 1 || (e.1.2.1 != 0 && decide (e.2 ≤ tailLook L (e.1.2.1 - 1))))

theorem tabMax_le_bound (T : SiteTable) (P : Nat × Nat × List Nat → Bool) (B : Nat)
    (h : ∀ e ∈ T, P e.1 = true → e.2 ≤ B) : tabMax T P ≤ B := by
  unfold tabMax
  suffices ∀ (T : SiteTable) (m : Nat), m ≤ B → (∀ e ∈ T, P e.1 = true → e.2 ≤ B) →
      T.foldl (fun m e => if P e.1 then max m e.2 else m) m ≤ B from this T 0 (Nat.zero_le _) h
  intro T
  induction T with
  | nil => intro m hm _; simpa using hm
  | cons e T ih =>
    intro m hm hT
    simp only [List.foldl_cons]
    apply ih
    · split
      · have := hT e (by simp) (by assumption); omega
      · exact hm
    · intro e' he' hp; exact hT e' (by simp [he']) hp

theorem tailEnv_le (T : SiteTable) (L : List (Nat × Nat)) (h : tailOk T L = true) (l : Nat) :
    tailEnv T (some l) ≤ tailLook L l := by
  unfold tailEnv
  apply tabMax_le_bound
  intro e he hp
  simp only [tailOk, List.all_eq_true] at h
  have he' := h e he
  simp only [Bool.and_eq_true, beq_iff_eq, destKey] at hp
  obtain ⟨h1, h2⟩ := hp
  simp only [h1, h2, bne_self_eq_false, Bool.false_or, Bool.and_eq_true, bne_iff_ne, ne_eq,
    decide_eq_true_eq] at he'
  simpa using he'.2

theorem tail1_ok_0 : tailOk wsT1_0 tail1 = true := by decide +kernel
theorem tail1_ok_1 : tailOk wsT1_1 tail1 = true := by decide +kernel
theorem tail1_ok_2 : tailOk wsT1_2 tail1 = true := by decide +kernel
theorem tail1_ok_3 : tailOk wsT1_3 tail1 = true := by decide +kernel
theorem tail1_ok_4 : tailOk wsT1_4 tail1 = true := by decide +kernel
theorem tail1_ok_5 : tailOk wsT1_5 tail1 = true := by decide +kernel
theorem tail1_ok_6 : tailOk wsT1_6 tail1 = true := by decide +kernel
theorem tail1_ok_7 : tailOk wsT1_7 tail1 = true := by decide +kernel
theorem tail1_ok_8 : tailOk wsT1_8 tail1 = true := by decide +kernel
theorem tail1_ok_9 : tailOk wsT1_9 tail1 = true := by decide +kernel
theorem tail1_ok_10 : tailOk wsT1_10 tail1 = true := by decide +kernel
theorem tail1_ok_11 : tailOk wsT1_11 tail1 = true := by decide +kernel
theorem tail1_ok_12 : tailOk wsT1_12 tail1 = true := by decide +kernel
theorem tail1_ok_13 : tailOk wsT1_13 tail1 = true := by decide +kernel
theorem tail1_ok_14 : tailOk wsT1_14 tail1 = true := by decide +kernel
theorem tail1_ok_15 : tailOk wsT1_15 tail1 = true := by decide +kernel
theorem tail1_ok_16 : tailOk wsT1_16 tail1 = true := by decide +kernel
theorem tail1_ok_17 : tailOk wsT1_17 tail1 = true := by decide +kernel
theorem tail1_ok_18 : tailOk wsT1_18 tail1 = true := by decide +kernel
theorem tail1_ok_19 : tailOk wsT1_19 tail1 = true := by decide +kernel
theorem tail1_ok_20 : tailOk wsT1_20 tail1 = true := by decide +kernel
theorem tail1_ok_21 : tailOk wsT1_21 tail1 = true := by decide +kernel
theorem tail1_ok_22 : tailOk wsT1_22 tail1 = true := by decide +kernel
theorem tail1_ok_23 : tailOk wsT1_23 tail1 = true := by decide +kernel
theorem tail1_ok_24 : tailOk wsT1_24 tail1 = true := by decide +kernel
theorem tail1_ok_25 : tailOk wsT1_25 tail1 = true := by decide +kernel
theorem tail1_ok_26 : tailOk wsT1_26 tail1 = true := by decide +kernel
theorem tail2_ok_0 : tailOk wsT2_0 tail2 = true := by decide +kernel
theorem tail2_ok_1 : tailOk wsT2_1 tail2 = true := by decide +kernel
theorem tail2_ok_2 : tailOk wsT2_2 tail2 = true := by decide +kernel
theorem tail2_ok_3 : tailOk wsT2_3 tail2 = true := by decide +kernel
theorem tail2_ok_4 : tailOk wsT2_4 tail2 = true := by decide +kernel
theorem tail2_ok_5 : tailOk wsT2_5 tail2 = true := by decide +kernel
theorem tail2_ok_6 : tailOk wsT2_6 tail2 = true := by decide +kernel

theorem tailOk_append (a b : SiteTable) (L : List (Nat × Nat)) :
    tailOk (a ++ b) L = (tailOk a L && tailOk b L) := by
  simp only [tailOk, List.all_append]

theorem tailOk_append_true {a b : SiteTable} {L : List (Nat × Nat)} (ha : tailOk a L = true)
    (hb : tailOk b L = true) : tailOk (a ++ b) L = true := by
  rw [tailOk_append, ha, hb]; rfl

theorem wsT1_split : wsT1 = wsT1_0 ++ wsT1_1 ++ wsT1_2 ++ wsT1_3 ++ wsT1_4 ++ wsT1_5 ++ wsT1_6 ++ wsT1_7 ++ wsT1_8 ++ wsT1_9 ++ wsT1_10 ++ wsT1_11 ++ wsT1_12 ++ wsT1_13 ++ wsT1_14 ++ wsT1_15 ++ wsT1_16 ++ wsT1_17 ++ wsT1_18 ++ wsT1_19 ++ wsT1_20 ++ wsT1_21 ++ wsT1_22 ++ wsT1_23 ++ wsT1_24 ++ wsT1_25 ++ wsT1_26 := rfl

theorem tail1_ok : tailOk wsT1 tail1 = true := by
  rw [wsT1_split]
  exact tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tail1_ok_0) tail1_ok_1) tail1_ok_2) tail1_ok_3) tail1_ok_4) tail1_ok_5) tail1_ok_6) tail1_ok_7) tail1_ok_8) tail1_ok_9) tail1_ok_10) tail1_ok_11) tail1_ok_12) tail1_ok_13) tail1_ok_14) tail1_ok_15) tail1_ok_16) tail1_ok_17) tail1_ok_18) tail1_ok_19) tail1_ok_20) tail1_ok_21) tail1_ok_22) tail1_ok_23) tail1_ok_24) tail1_ok_25) tail1_ok_26

theorem wsT2_split : wsT2 = wsT2_0 ++ wsT2_1 ++ wsT2_2 ++ wsT2_3 ++ wsT2_4 ++ wsT2_5 ++ wsT2_6 := rfl

theorem tail2_ok : tailOk wsT2 tail2 = true := by
  rw [wsT2_split]
  exact tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tailOk_append_true (tail2_ok_0) tail2_ok_1) tail2_ok_2) tail2_ok_3) tail2_ok_4) tail2_ok_5) tail2_ok_6

/-- The Loop tail surcharge of a callee is within its certified table entry. -/
theorem wsTail_le_tailSitesL (l : Nat) : wsTail (some l) ≤ tailSitesL l := by
  have h1 := tailEnv_le wsT1 tail1 tail1_ok l
  have h2 := tailEnv_le wsT2 tail2 tail2_ok l
  simp only [wsTail, tailSitesL]
  omega

theorem wsTail_none : wsTail none = 0 := by decide +kernel

/-- The source-side copy of the tail table is the certified one. -/
theorem tailSitesL_src (l : Nat) : tailSitesL l = srcTailSitesL l := rfl

theorem wsTail_le_srcTailSitesL (l : Nat) : wsTail (some l) ≤ srcTailSitesL l :=
  tailSitesL_src l ▸ wsTail_le_tailSitesL l

#print axioms tailEnv_le
#print axioms wsTail_le_tailSitesL
#print axioms wsTail_none
#print axioms wsTail_le_srcTailSitesL
end InitECandidate.Runtime.FineCost
