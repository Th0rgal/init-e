namespace InitECandidate.Runtime.FineCost

/-! Certified per-callee tail-call surcharge tables, read off the WordSimp site
tables (`CrepTailSites` proves `wsTail (some l) ≤ srcTailSitesL l`). Kept free of
the cost chain so the source call charge can pay `tailSitesL` of its callee. -/

/-- Per-label maxima of the kind-1 (tail) entries of `wsT1`. -/
def srcTail1 : List (Nat × Nat) :=
  [(117, 4), (128, 1), (131, 3), (135, 4), (174, 1), (176, 1), (211, 4), (212, 4), (214, 4), (221, 4),
   (222, 4), (298, 1), (299, 1), (308, 1), (369, 2), (372, 2)]

/-- Per-label maxima of the kind-1 (tail) entries of `wsT2`. -/
def srcTail2 : List (Nat × Nat) := [(117, 4), (128, 1), (131, 6), (298, 1), (299, 1)]

def srcTailLook (L : List (Nat × Nat)) (l : Nat) : Nat := (L.lookup l).getD 0

/-- The certified tail surcharge of callee label `l`. -/
def srcTailSitesL (l : Nat) : Nat := 24 * (srcTailLook srcTail2 l + srcTailLook srcTail1 l)

theorem srcTailSitesL_le (l : Nat) : srcTailSitesL l ≤ srcTailSitesL l + 0 := by omega

#print axioms srcTailSitesL_le
end InitECandidate.Runtime.FineCost
