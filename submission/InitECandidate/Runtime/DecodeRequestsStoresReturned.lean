import InitECandidate.Runtime.DecodeRequestsBodyBound
import InitECandidate.Runtime.SszSplitVarListEval
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned run through one request-cell store exposes the store. -/
theorem reqStore_returned {σ : Type} (t post : PanSemStateFiniteExact 64 σ) (offset : BitVec 64)
    (value : ExpHOL 64) (rest : ProgHOL 64) (rq x : BitVec 64) (v : ValueHOL 64)
    (hrq : t.locals.lookup (ofString "rq") = some (.val (.word rq)))
    (hx : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) value = some (.val (.word x)))
    (run : evaluateHOLFiniteState t (reqStore offset value rest) = (some (.returned v), post)) :
    t.memaddrs (rq + offset) ∧
      evaluateHOLFiniteState ({t with memory := wmem t.memory (rq + offset) x} : PanSemStateFiniteExact 64 σ) rest =
        (some (.returned v), post) := by
  have addr : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a))
      (.op .add [sszLocal "rq", .const offset]) = some (.val (.word (rq + offset))) := by
    simp [sszLocal, evalHOLExact, evalListHOLExact, hrq, wordOpHOL, wordOp, valueIsWord, valueWord]
  unfold reqStore at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  by_cases dom : t.memaddrs (rq + offset)
  · rw [sszStore_in t _ _ _ _ addr hx dom] at run
    exact ⟨dom, run⟩
  · rw [sszStore_out t _ _ _ _ addr hx dom] at run
    simp at run

#print axioms reqStore_returned

def memWrites (m : BitVec 64 → HolWordLab 64) (base : BitVec 64) : List (BitVec 64 × BitVec 64) → BitVec 64 → HolWordLab 64
  | [] => m
  | x :: xs => memWrites (wmem m (base + x.1) x.2) base xs

theorem memWrites_frame (m : BitVec 64 → HolWordLab 64) (base : BitVec 64) (l : List (BitVec 64 × BitVec 64)) (a : BitVec 64)
    (h : ∀ x ∈ l, a ≠ base + x.1) : memWrites m base l a = m a := by
  induction l generalizing m with
  | nil => rfl
  | cons x xs ih =>
    simp only [memWrites]
    rw [ih _ (fun y hy => h y (List.mem_cons_of_mem _ hy))]
    simp only [wmem, if_neg (h x (by simp))]

theorem memWrites_cell (m : BitVec 64 → HolWordLab 64) (base : BitVec 64) (l : List (BitVec 64 × BitVec 64))
    (nodup : (l.map Prod.fst).Nodup) (x : BitVec 64 × BitVec 64) (hx : x ∈ l) :
    memWrites m base l (base + x.1) = .word x.2 := by
  induction l generalizing m with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [List.map_cons, List.nodup_cons] at nodup
    simp only [memWrites]
    rcases List.mem_cons.mp hx with rfl | inys
    · rw [memWrites_frame _ _ _ _ (fun z hz e => nodup.1 (by
        rw [BitVec.add_right_inj] at e; rw [e]; exact List.mem_map_of_mem hz))]
      simp [wmem]
    · exact ih _ nodup.2 inys

def reqCellValues (p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4 : BitVec 64) : List (BitVec 64 × BitVec 64) :=
  [(0, p + o0), (8, n0), (16, p + o1), (24, n1), (32, p + o2), (40, n2), (48, p + o3), (56, n3),
    (64, p + o4), (72, n4)]

theorem reqCellValues_nodup (p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4 : BitVec 64) :
    ((reqCellValues p o0 o1 o2 o3 o4 n0 n1 n2 n3 n4).map Prod.fst).Nodup := by
  simp [reqCellValues]

theorem reqVar_eval {σ : Type} (t : PanSemStateFiniteExact 64 σ) (name : String) (x : BitVec 64)
    (h : t.locals.lookup (ofString name) = some (.val (.word x))) :
    @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (sszLocal name) =
      some (.val (.word x)) := by
  simp [sszLocal, evalHOLExact, h]

/-- A returned run of the request stores returns rq, writes exactly the ten
request cells (all in the domain), and keeps globals and domain. -/
theorem reqStores_returned {σ : Type} (t post : PanSemStateFiniteExact 64 σ)
    (rq p O0 O1 O2 O3 O4 N0 N1 N2 N3 N4 : BitVec 64) (v : ValueHOL 64)
    (hrq : t.locals.lookup (ofString "rq") = some (.val (.word rq)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word p)))
    (ho0 : t.locals.lookup (ofString "o0") = some (.val (.word O0)))
    (ho1 : t.locals.lookup (ofString "o1") = some (.val (.word O1)))
    (ho2 : t.locals.lookup (ofString "o2") = some (.val (.word O2)))
    (ho3 : t.locals.lookup (ofString "o3") = some (.val (.word O3)))
    (ho4 : t.locals.lookup (ofString "o4") = some (.val (.word O4)))
    (hn0 : t.locals.lookup (ofString "n0") = some (.val (.word N0)))
    (hn1 : t.locals.lookup (ofString "n1") = some (.val (.word N1)))
    (hn2 : t.locals.lookup (ofString "n2") = some (.val (.word N2)))
    (hn3 : t.locals.lookup (ofString "n3") = some (.val (.word N3)))
    (hn4 : t.locals.lookup (ofString "n4") = some (.val (.word N4)))
    (run : evaluateHOLFiniteState t reqStores = (some (.returned v), post)) :
    v = .val (.word rq) ∧
      (∀ x ∈ reqCellValues p O0 O1 O2 O3 O4 N0 N1 N2 N3 N4, t.memaddrs (rq + x.1)) ∧
      post.memory = memWrites t.memory rq (reqCellValues p O0 O1 O2 O3 O4 N0 N1 N2 N3 N4) ∧
      post.globals = t.globals ∧ post.memaddrs = t.memaddrs := by
  unfold reqStores at run
  obtain ⟨d0, r0⟩ := reqStore_returned t post 0 _ _ rq (p + O0) v hrq (sszSplit_sum t p O0 "p" "o0" hp ho0) run
  generalize ht0 : ({t with memory := wmem t.memory (rq + 0) (p + O0)} : PanSemStateFiniteExact 64 σ) = t0 at r0
  have l0 : t0.locals = t.locals := by rw [← ht0]
  obtain ⟨d1, r1⟩ := reqStore_returned t0 post 8 _ _ rq N0 v (by rw [l0]; exact hrq) (reqVar_eval t0 "n0" N0 (by rw [l0]; exact hn0)) r0
  generalize ht1 : ({t0 with memory := wmem t0.memory (rq + 8) N0} : PanSemStateFiniteExact 64 σ) = t1 at r1
  have l1 : t1.locals = t.locals := by rw [← ht1]; exact l0
  obtain ⟨d2, r2⟩ := reqStore_returned t1 post 16 _ _ rq (p + O1) v (by rw [l1]; exact hrq) (sszSplit_sum t1 p O1 "p" "o1" (by rw [l1]; exact hp) (by rw [l1]; exact ho1)) r1
  generalize ht2 : ({t1 with memory := wmem t1.memory (rq + 16) (p + O1)} : PanSemStateFiniteExact 64 σ) = t2 at r2
  have l2 : t2.locals = t.locals := by rw [← ht2]; exact l1
  obtain ⟨d3, r3⟩ := reqStore_returned t2 post 24 _ _ rq N1 v (by rw [l2]; exact hrq) (reqVar_eval t2 "n1" N1 (by rw [l2]; exact hn1)) r2
  generalize ht3 : ({t2 with memory := wmem t2.memory (rq + 24) N1} : PanSemStateFiniteExact 64 σ) = t3 at r3
  have l3 : t3.locals = t.locals := by rw [← ht3]; exact l2
  obtain ⟨d4, r4⟩ := reqStore_returned t3 post 32 _ _ rq (p + O2) v (by rw [l3]; exact hrq) (sszSplit_sum t3 p O2 "p" "o2" (by rw [l3]; exact hp) (by rw [l3]; exact ho2)) r3
  generalize ht4 : ({t3 with memory := wmem t3.memory (rq + 32) (p + O2)} : PanSemStateFiniteExact 64 σ) = t4 at r4
  have l4 : t4.locals = t.locals := by rw [← ht4]; exact l3
  obtain ⟨d5, r5⟩ := reqStore_returned t4 post 40 _ _ rq N2 v (by rw [l4]; exact hrq) (reqVar_eval t4 "n2" N2 (by rw [l4]; exact hn2)) r4
  generalize ht5 : ({t4 with memory := wmem t4.memory (rq + 40) N2} : PanSemStateFiniteExact 64 σ) = t5 at r5
  have l5 : t5.locals = t.locals := by rw [← ht5]; exact l4
  obtain ⟨d6, r6⟩ := reqStore_returned t5 post 48 _ _ rq (p + O3) v (by rw [l5]; exact hrq) (sszSplit_sum t5 p O3 "p" "o3" (by rw [l5]; exact hp) (by rw [l5]; exact ho3)) r5
  generalize ht6 : ({t5 with memory := wmem t5.memory (rq + 48) (p + O3)} : PanSemStateFiniteExact 64 σ) = t6 at r6
  have l6 : t6.locals = t.locals := by rw [← ht6]; exact l5
  obtain ⟨d7, r7⟩ := reqStore_returned t6 post 56 _ _ rq N3 v (by rw [l6]; exact hrq) (reqVar_eval t6 "n3" N3 (by rw [l6]; exact hn3)) r6
  generalize ht7 : ({t6 with memory := wmem t6.memory (rq + 56) N3} : PanSemStateFiniteExact 64 σ) = t7 at r7
  have l7 : t7.locals = t.locals := by rw [← ht7]; exact l6
  obtain ⟨d8, r8⟩ := reqStore_returned t7 post 64 _ _ rq (p + O4) v (by rw [l7]; exact hrq) (sszSplit_sum t7 p O4 "p" "o4" (by rw [l7]; exact hp) (by rw [l7]; exact ho4)) r7
  generalize ht8 : ({t7 with memory := wmem t7.memory (rq + 64) (p + O4)} : PanSemStateFiniteExact 64 σ) = t8 at r8
  have l8 : t8.locals = t.locals := by rw [← ht8]; exact l7
  obtain ⟨d9, r9⟩ := reqStore_returned t8 post 72 _ _ rq N4 v (by rw [l8]; exact hrq) (reqVar_eval t8 "n4" N4 (by rw [l8]; exact hn4)) r8
  generalize ht9 : ({t8 with memory := wmem t8.memory (rq + 72) N4} : PanSemStateFiniteExact 64 σ) = t9 at r9
  have l9 : t9.locals = t.locals := by rw [← ht9]; exact l8
  have hrq9 : t9.locals.lookup (ofString "rq") = some (.val (.word rq)) := by rw [l9]; exact hrq
  rw [evaluateHOLFiniteState_return] at r9
  simp only [sszLocal, evalHOLExact, lookupKvarHOLExact, hrq9, shapeOfHOLExact] at r9
  simp at r9
  obtain ⟨rfl, rfl⟩ := r9
  subst ht9 ht8 ht7 ht6 ht5 ht4 ht3 ht2 ht1 ht0
  refine ⟨rfl, ?_, rfl, rfl, rfl⟩
  intro x hx
  simp only [reqCellValues, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

#print axioms reqStores_returned
end InitECandidate.Runtime
