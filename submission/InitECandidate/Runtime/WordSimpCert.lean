import InitECandidate.Runtime.WordSimpFuel
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordSimp

/-- `constFpLoop` with the kernel-evaluable expression folder. -/
noncomputable def cfLoopF :
    WordLangProgHOL (BitVec 64) → Spt (BitVec 64) → WordLangProgHOL (BitVec 64) × Spt (BitVec 64)
  | .move pri moves, cs => (.move pri moves, constFpMoveCs moves cs cs)
  | .inst i, cs => (.inst i, constFpInstCs i cs)
  | .assign v e, cs =>
      match cfpX e cs with
      | .const c => (.assign v (.const c), sptInsert v c cs)
      | e' => (.assign v e', sptDelete v cs)
  | .get v name, cs => (.get v name, sptDelete v cs)
  | .opCurrHeap b v w, cs => (.opCurrHeap b v w, sptDelete v cs)
  | .mustTerminate p, cs =>
      let r := cfLoopF p cs
      (.mustTerminate r.1, r.2)
  | .seq p1 p2, cs =>
      let r1 := cfLoopF p1 cs
      let r2 := cfLoopF p2 r1.2
      (.seq r1.1 r2.1, r2.2)
  | .ite cmp lhs rhs p1 p2, cs =>
      match sptLookup lhs cs, getVarImmCs rhs cs with
      | some clhs, some crhs =>
          if Flapjack.Compiler.Encoders.Asm.wordCmpHOL cmp clhs crhs then cfLoopF p1 cs else cfLoopF p2 cs
      | _, _ =>
          let r1 := cfLoopF p1 cs
          let r2 := cfLoopF p2 cs
          (.ite cmp lhs rhs r1.1 r2.1, sptInterEq r1.2 r2.2)
  | .call ret dest args handler, cs =>
      match ret with
      | none => (smartSeqHOL (dropConsts cs args) (.call ret dest args handler), sptFilterV isGcConst cs)
      | some (n, names, retHandler, l1, l2) =>
          match handler with
          | none =>
              let cs' := deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names)))
              let r := cfLoopF retHandler cs'
              (smartSeqHOL (dropConsts cs args) (.call (some (n, names, r.1, l1, l2)) dest args handler), r.2)
          | some _ => (smartSeqHOL (dropConsts cs args) (.call ret dest args handler), .ln)
  | .ffi x0 x1 x2 x3 x4 names, cs =>
      (smartSeqHOL (dropConsts cs [x1, x2, x3, x4]) (.ffi x0 x1 x2 x3 x4 names), sptInter cs (allNames names))
  | .locValue v x3, cs => (.locValue v x3, sptDelete v cs)
  | .alloc n names, cs =>
      (smartSeqHOL (dropConsts cs [n]) (.alloc n names), sptFilterV isGcConst (sptInter cs (allNames names)))
  | .storeConsts a b c d ws, cs =>
      (.storeConsts a b c d ws, sptDelete a (sptDelete b (sptDelete c (sptDelete d cs))))
  | .install r1 r2 r3 r4 names, cs =>
      (smartSeqHOL (dropConsts cs [r1, r2, r3, r4]) (.install r1 r2 r3 r4 names),
        sptDelete r1 (sptFilterV isGcConst (sptInter cs (allNames names))))
  | .store e v, cs => (.store (cfpX e cs) v, cs)
  | .shareInst .load v e, cs => (.shareInst .load v (cfpX e cs), sptDelete v cs)
  | .shareInst .load8 v e, cs => (.shareInst .load8 v (cfpX e cs), sptDelete v cs)
  | .shareInst .load16 v e, cs => (.shareInst .load16 v (cfpX e cs), sptDelete v cs)
  | .shareInst .load32 v e, cs => (.shareInst .load32 v (cfpX e cs), sptDelete v cs)
  | .shareInst .store v e, cs => (.shareInst .store v (cfpX e cs), cs)
  | .shareInst .store8 v e, cs => (.shareInst .store8 v (cfpX e cs), cs)
  | .shareInst .store16 v e, cs => (.shareInst .store16 v (cfpX e cs), cs)
  | .shareInst .store32 v e, cs => (.shareInst .store32 v (cfpX e cs), cs)
  | .loop names body exitNames, _ => (.loop names (cfLoopF body .ln).1 exitNames, .ln)
  | p, cs => (p, cs)

theorem cfLoopF_eq : ∀ (p : WordLangProgHOL (BitVec 64)) (cs : Spt (BitVec 64)), cfLoopF p cs = constFpLoop p cs
  | .assign v e, cs => by
      simp only [cfLoopF, constFpLoop, cfpX_eq]
      generalize constFpExp e cs = E
      split
      · rfl
      · split
        · exfalso; simp_all
        · rfl
  | .mustTerminate p, cs => by simp only [cfLoopF, constFpLoop, cfLoopF_eq p cs]
  | .seq p1 p2, cs => by simp only [cfLoopF, constFpLoop, cfLoopF_eq p1 cs, cfLoopF_eq p2]
  | .ite cmp lhs rhs p1 p2, cs => by
      simp only [cfLoopF, constFpLoop, cfLoopF_eq p1 cs, cfLoopF_eq p2 cs]
      rcases sptLookup lhs cs with _ | a <;> rcases getVarImmCs rhs cs with _ | b <;> rfl
  | .call ret dest args handler, cs => by
      rcases ret with _ | ⟨n, names, rh, l1, l2⟩
      · simp only [cfLoopF, constFpLoop]
      · rcases handler with _ | h
        · simp only [cfLoopF, constFpLoop, cfLoopF_eq rh]
        · simp only [cfLoopF, constFpLoop]
  | .store e v, cs => by simp only [cfLoopF, constFpLoop, cfpX_eq]
  | .shareInst op v e, cs => by cases op <;> simp only [cfLoopF, constFpLoop, cfpX_eq]
  | .loop names body exitNames, cs => by simp only [cfLoopF, constFpLoop, cfLoopF_eq body]
  | .move _ _, _ | .inst _, _ | .get _ _, _ | .opCurrHeap _ _ _, _ | .ffi _ _ _ _ _ _, _ | .locValue _ _, _
  | .alloc _ _, _ | .storeConsts _ _ _ _ _, _ | .install _ _ _ _ _, _ | .skip, _ | .set _ _, _ | .tick, _
  | .raise _, _ | .return _ _, _ | .break _, _ | .continue _, _ | .codeBufferWrite _ _, _
  | .dataBufferWrite _ _, _ => by simp only [cfLoopF, constFpLoop]

/-- Site key of a surcharged node: returning calls by return label, tail calls
by (destination, arguments), alloc/ffi/install by their registers. -/
def siteKey : WordLangProgHOL (BitVec 64) → Option (Nat × Nat × List Nat)
  | .call (some (_, _, _, l1, l2)) _ _ _ => some (0, l1, [l2])
  | .call none dest args _ => some (1, (match dest with | none => 0 | some d => d + 1), args)
  | .alloc n _ => some (2, n, [])
  | .ffi _ x1 x2 x3 x4 _ => some (3, 0, [x1, x2, x3, x4])
  | .install r1 r2 r3 r4 _ => some (4, 0, [r1, r2, r3, r4])
  | _ => none

abbrev SiteTable := List ((Nat × Nat × List Nat) × Nat)

def tLookup (T : SiteTable) (k : Nat × Nat × List Nat) : Nat :=
  match T.find? (fun e => e.1 == k) with
  | some e => e.2
  | none => 0

/-- Node surcharge read from a site table. -/
def surOf (T : SiteTable) (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match siteKey p with
  | some k => tLookup T k
  | none => 0

theorem surShape_surOf (T : SiteTable) : SurShape (surOf T) := by
  refine ⟨fun p hp => ?_, fun _ _ _ _ _ _ _ _ _ => rfl, fun r _ _ _ _ _ _ _ => ?_⟩
  · cases p <;> simp_all [isSurNode, surOf, siteKey]
  · rcases r with _ | ⟨_, _, _, _, _⟩ <;> rfl

/-- Kernel-checkable `CfOk`. -/
noncomputable def cfOkB (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T : SiteTable) :
    WordLangProgHOL (BitVec 64) → Spt (BitVec 64) → Bool
  | .assign v e, cs => decide (iselXF c (.assign v (cfpX e cs)) ≤ iselXF c (.assign v e))
  | .store e v, cs => decide (iselXF c (.store (cfpX e cs) v) ≤ iselXF c (.store e v))
  | .shareInst op v e, cs => decide (iselXF c (.shareInst op v (cfpX e cs)) ≤ iselXF c (.shareInst op v e))
  | .mustTerminate p, cs => cfOkB c T p cs
  | .seq p1 p2, cs => cfOkB c T p1 cs && cfOkB c T p2 (cfLoopF p1 cs).2
  | .ite cmp lhs rhs p1 p2, cs =>
      match sptLookup lhs cs, getVarImmCs rhs cs with
      | some a, some b => if Compiler.Encoders.Asm.wordCmpHOL cmp a b then cfOkB c T p1 cs else cfOkB c T p2 cs
      | _, _ => cfOkB c T p1 cs && cfOkB c T p2 cs
  | .call none dest args h, cs => decide (dropN cs args ≤ surOf T (.call none dest args h))
  | .call (some (n, names, rh, l1, l2)) dest args none, cs =>
      decide (dropN cs args ≤ surOf T (.call (some (n, names, rh, l1, l2)) dest args none)) &&
        cfOkB c T rh (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names))))
  | .call (some r) dest args (some h), cs => decide (dropN cs args ≤ surOf T (.call (some r) dest args (some h)))
  | .ffi x0 x1 x2 x3 x4 names, cs => decide (dropN cs [x1, x2, x3, x4] ≤ surOf T (.ffi x0 x1 x2 x3 x4 names))
  | .alloc n names, cs => decide (dropN cs [n] ≤ surOf T (.alloc n names))
  | .install r1 r2 r3 r4 names, cs => decide (dropN cs [r1, r2, r3, r4] ≤ surOf T (.install r1 r2 r3 r4 names))
  | .loop _ body _, _ => cfOkB c T body .ln
  | _, _ => true

theorem cfOkB_sound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T : SiteTable) :
    ∀ (p : WordLangProgHOL (BitVec 64)) (cs : Spt (BitVec 64)), cfOkB c T p cs = true → CfOk c (surOf T) p cs
  | .assign v e, cs, h => by
      simp only [cfOkB, decide_eq_true_eq, cfpX_eq] at h
      rw [iselXF_eq c (.assign v _) rfl, iselXF_eq c (.assign v e) rfl] at h; exact h
  | .store e v, cs, h => by
      simp only [cfOkB, decide_eq_true_eq, cfpX_eq] at h
      rw [iselXF_eq c (.store _ v) rfl, iselXF_eq c (.store e v) rfl] at h; exact h
  | .shareInst op v e, cs, h => by
      simp only [cfOkB, decide_eq_true_eq, cfpX_eq] at h
      rw [iselXF_eq c (.shareInst op v _) rfl, iselXF_eq c (.shareInst op v e) rfl] at h; exact h
  | .mustTerminate p, cs, h => by simp only [cfOkB] at h; exact cfOkB_sound c T p cs h
  | .seq p1 p2, cs, h => by
      simp only [cfOkB, Bool.and_eq_true, cfLoopF_eq] at h
      exact ⟨cfOkB_sound c T p1 cs h.1, cfOkB_sound c T p2 _ h.2⟩
  | .ite cmp lhs rhs p1 p2, cs, h => by
      simp only [cfOkB] at h
      simp only [CfOk]
      rcases hA : sptLookup lhs cs with _ | a <;> rcases hB : getVarImmCs rhs cs with _ | b <;>
        simp only [hA, hB, Bool.and_eq_true] at h ⊢
      all_goals first
        | exact ⟨cfOkB_sound c T p1 cs h.1, cfOkB_sound c T p2 cs h.2⟩
        | (split_ifs at h ⊢ <;> first | exact cfOkB_sound c T p1 cs h | exact cfOkB_sound c T p2 cs h)
  | .call none dest args hh, cs, h => by simp only [cfOkB, decide_eq_true_eq] at h; exact h
  | .call (some (n, names, rh, l1, l2)) dest args none, cs, h => by
      simp only [cfOkB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨h.1, cfOkB_sound c T rh _ h.2⟩
  | .call (some r) dest args (some hh), cs, h => by simp only [cfOkB, decide_eq_true_eq] at h; exact h
  | .ffi x0 x1 x2 x3 x4 names, cs, h => by simp only [cfOkB, decide_eq_true_eq] at h; exact h
  | .alloc n names, cs, h => by simp only [cfOkB, decide_eq_true_eq] at h; exact h
  | .install r1 r2 r3 r4 names, cs, h => by simp only [cfOkB, decide_eq_true_eq] at h; exact h
  | .loop _ body _, cs, h => by simp only [cfOkB] at h; exact cfOkB_sound c T body _ h
  | .move _ _, _, _ | .inst _, _, _ | .get _ _, _, _ | .opCurrHeap _ _ _, _, _ | .locValue _ _, _, _
  | .storeConsts _ _ _ _ _, _, _ | .skip, _, _ | .set _ _, _, _ | .tick, _, _ | .raise _, _, _
  | .return _ _, _, _ | .break _, _, _ | .continue _, _, _ | .codeBufferWrite _ _, _, _
  | .dataBufferWrite _ _, _, _ => by unfold CfOk; trivial

noncomputable def constFpF (p : WordLangProgHOL (BitVec 64)) : WordLangProgHOL (BitVec 64) := (cfLoopF p .ln).1

theorem constFpF_eq (p : WordLangProgHOL (BitVec 64)) : constFpF p = constFp p := by
  simp only [constFpF, constFp, cfLoopF_eq]

/-- `tryIfHoist2` with the kernel-evaluable constant folder. -/
noncomputable def tryIfHoist2F :
    Nat → WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) →
      WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) → Option (WordLangProgHOL (BitVec 64))
  | 0, _, _, _, _ => none
  | n + 1, p1, interm, dummy, p2 =>
      match p1 with
      | .ite cmp lhs rhs br1 br2 =>
          let res1 := destRaiseNum (destSeq (constFpF (.seq (.seq br1 interm) dummy))).2
          if res1 = 0 then none
          else
            let res2 := destRaiseNum (destSeq (constFpF (.seq (.seq br2 interm) dummy))).2
            if res1 + res2 ≠ 3 then none
            else some (constFpF (.ite cmp lhs rhs (.seq (.seq br1 interm) p2) (.seq (.seq br2 interm) p2)))
      | .seq p3 p4 =>
          match destIf p4 with
          | some (cmp, lhs, rhs, br1, br2) =>
              let res1 := destRaiseNum (destSeq (constFpF (.seq (.seq br1 interm) dummy))).2
              if res1 = 0 then none
              else
                let res2 := destRaiseNum (destSeq (constFpF (.seq (.seq br2 interm) dummy))).2
                if res1 + res2 ≠ 3 then none
                else some (.seq p3 (constFpF (.ite cmp lhs rhs (.seq (.seq br1 interm) p2)
                  (.seq (.seq br2 interm) p2))))
          | none =>
              if isSimple p4 then tryIfHoist2F n p3 (.seq p4 interm) dummy p2
              else none
      | _ => none

theorem tryIfHoist2F_eq : ∀ (n : Nat) (p1 interm dummy p2 : WordLangProgHOL (BitVec 64)),
    tryIfHoist2F n p1 interm dummy p2 = tryIfHoist2 n p1 interm dummy p2
  | 0, _, _, _, _ => by simp only [tryIfHoist2F, tryIfHoist2]
  | n + 1, p1, interm, dummy, p2 => by
      simp only [tryIfHoist2F, tryIfHoist2, constFpF_eq]
      cases p1 <;> try rfl
      case seq p3 p4 =>
        simp only
        rcases destIf p4 with _ | ⟨cmp, lhs, rhs, br1, br2⟩
        · simp only [tryIfHoist2F_eq n p3]
        · rfl

noncomputable def tryIfHoist1F (p1 p2 : WordLangProgHOL (BitVec 64)) : Option (WordLangProgHOL (BitVec 64)) :=
  match destIf p2 with
  | none => none
  | some (cmp, lhs, rhs, _, _) =>
      tryIfHoist2F rewriteDuplicateIfMaxReassoc p1 .skip (.ite cmp lhs rhs (.raise 1) (.raise 2)) p2

theorem tryIfHoist1F_eq (p1 p2 : WordLangProgHOL (BitVec 64)) : tryIfHoist1F p1 p2 = tryIfHoist1 p1 p2 := by
  simp only [tryIfHoist1F, tryIfHoist1, tryIfHoist2F_eq]
  rcases destIf p2 with _ | ⟨_, _, _, _, _⟩ <;> rfl

/-- `simpDuplicateIf` with the kernel-evaluable hoist. -/
noncomputable def sdiF : WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64)
  | .mustTerminate q => .mustTerminate (sdiF q)
  | .call retProg dest args handler =>
      .call
        (match retProg with
          | none => none
          | some (x1, x2, q1, x3, x4) => some (x1, x2, sdiF q1, x3, x4))
        dest args
        (match handler with
          | none => none
          | some (y1, q2, y2, y3) => some (y1, sdiF q2, y2, y3))
  | .ite cmp lhs rhs br1 br2 => .ite cmp lhs rhs (sdiF br1) (sdiF br2)
  | .seq p1 p2 =>
      match tryIfHoist1F (sdiF p1) (sdiF p2) with
      | none => .seq (sdiF p1) (sdiF p2)
      | some p3 => seqAssoc .skip p3
  | .loop names body exitNames => .loop names (sdiF body) exitNames
  | p => p

theorem sdiF_eq : ∀ p : WordLangProgHOL (BitVec 64), sdiF p = simpDuplicateIf p
  | .mustTerminate q => by simp only [sdiF, simpDuplicateIf, sdiF_eq q]
  | .call ret dest args h => by
      rcases ret with _ | ⟨x1, x2, q1, x3, x4⟩ <;> rcases h with _ | ⟨y1, q2, y2, y3⟩ <;>
        simp only [sdiF, simpDuplicateIf, sdiF_eq]
  | .ite cmp lhs rhs a b => by simp only [sdiF, simpDuplicateIf, sdiF_eq a, sdiF_eq b]
  | .seq p1 p2 => by
      simp only [sdiF, simpDuplicateIf, sdiF_eq p1, sdiF_eq p2, tryIfHoist1F_eq]
      rcases tryIfHoist1 (simpDuplicateIf p1) (simpDuplicateIf p2) <;> rfl
  | .loop names body exits => by simp only [sdiF, simpDuplicateIf, sdiF_eq body]
  | .skip | .move _ _ | .inst _ | .assign _ _ | .get _ _ | .set _ _ | .store _ _ | .alloc _ _
  | .storeConsts _ _ _ _ _ | .raise _ | .return _ _ | .break _ | .continue _ | .tick | .opCurrHeap _ _ _
  | .locValue _ _ | .install _ _ _ _ _ | .codeBufferWrite _ _ | .dataBufferWrite _ _ | .ffi _ _ _ _ _ _
  | .shareInst _ _ _ => by simp only [sdiF, simpDuplicateIf]

/-! Site tables: max-merge, subtraction and pointwise order. -/

def tMax (T : SiteTable) (k : Nat × Nat × List Nat) (v : Nat) : SiteTable :=
  if tLookup T k ≥ v then T else (k, v) :: T

def tsub (T H : SiteTable) : SiteTable := T.map (fun e => (e.1, e.2 - tLookup H e.1))

def leTable (H T : SiteTable) : Bool := H.all (fun e => decide (e.2 ≤ tLookup T e.1))

theorem tLookup_nil (k : Nat × Nat × List Nat) : tLookup [] k = 0 := rfl

theorem tLookup_cons (e : (Nat × Nat × List Nat) × Nat) (T : SiteTable) (k : Nat × Nat × List Nat) :
    tLookup (e :: T) k = if e.1 == k then e.2 else tLookup T k := by
  unfold tLookup
  rw [List.find?_cons]
  by_cases he : e.1 == k
  · simp only [he, if_true]
  · simp only [he, Bool.false_eq_true, if_false]

theorem tLookup_tsub (T H : SiteTable) (k : Nat × Nat × List Nat) :
    tLookup (tsub T H) k = tLookup T k - tLookup H k := by
  induction T with
  | nil => simp [tsub, tLookup_nil]
  | cons e T ih =>
    simp only [tsub, List.map_cons, tLookup_cons] at ih ⊢
    by_cases he : e.1 == k
    · simp only [he, if_true]; simp only [beq_iff_eq] at he; rw [he]
    · simp only [he, Bool.false_eq_true, if_false]; exact ih

theorem leTable_sound {H T : SiteTable} (h : leTable H T = true) (k : Nat × Nat × List Nat) :
    tLookup H k ≤ tLookup T k := by
  simp only [leTable, List.all_eq_true, decide_eq_true_eq] at h
  induction H with
  | nil => simp [tLookup_nil]
  | cons e H ih =>
    rw [tLookup_cons]
    by_cases he : e.1 == k
    · simp only [he, if_true]; simp only [beq_iff_eq] at he
      have := h e (List.mem_cons_self ..); rw [he] at this; exact this
    · simp only [he, Bool.false_eq_true, if_false]
      exact ih (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem surOf_tsub (T H : SiteTable) (q : WordLangProgHOL (BitVec 64)) :
    surOf (tsub T H) q = surOf T q - surOf H q := by
  simp only [surOf]; split <;> simp [tLookup_tsub]

theorem surOf_le {H T : SiteTable} (h : leTable H T = true) (q : WordLangProgHOL (BitVec 64)) :
    surOf H q ≤ surOf T q := by
  simp only [surOf]; split
  · exact leTable_sound h _
  · exact Nat.le_refl 0

/-- Constant re-assignment counts of one constant-folding run, as a site table. -/
noncomputable def dropTab (T : SiteTable) : WordLangProgHOL (BitVec 64) → Spt (BitVec 64) → SiteTable
  | .mustTerminate q, cs => dropTab T q cs
  | .seq p1 p2, cs => dropTab (dropTab T p1 cs) p2 (cfLoopF p1 cs).2
  | .ite cmp lhs rhs p1 p2, cs =>
      match sptLookup lhs cs, getVarImmCs rhs cs with
      | some a, some b => if Compiler.Encoders.Asm.wordCmpHOL cmp a b then dropTab T p1 cs else dropTab T p2 cs
      | _, _ => dropTab (dropTab T p1 cs) p2 cs
  | .call none dest args h, cs => match siteKey (.call none dest args h) with
      | some k => tMax T k (dropN cs args) | none => T
  | .call (some (n, names, rh, l1, l2)) dest args none, cs =>
      dropTab (match siteKey (.call (some (n, names, rh, l1, l2)) dest args none) with
        | some k => tMax T k (dropN cs args) | none => T) rh
        (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names))))
  | .call (some r) dest args (some h), cs => match siteKey (.call (some r) dest args (some h)) with
      | some k => tMax T k (dropN cs args) | none => T
  | .ffi x0 x1 x2 x3 x4 names, cs => tMax T (3, 0, [x1, x2, x3, x4]) (dropN cs [x1, x2, x3, x4])
  | .alloc n names, cs => tMax T (2, n, []) (dropN cs [n])
  | .install r1 r2 r3 r4 names, cs => tMax T (4, 0, [r1, r2, r3, r4]) (dropN cs [r1, r2, r3, r4])
  | .loop _ body _, _ => dropTab T body .ln
  | _, _ => T

/-- The hoisted `ite` a successful `tryIfHoist2` folds (mirrors `HoistOk2`). -/
def hoistIte2 : Nat → WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) →
    WordLangProgHOL (BitVec 64) → Option (WordLangProgHOL (BitVec 64))
  | 0, _, _, _, _ => none
  | n + 1, p1, interm, dummy, p2 =>
      match p1 with
      | .ite cmp lhs rhs br1 br2 => some (.ite cmp lhs rhs (.seq (.seq br1 interm) p2) (.seq (.seq br2 interm) p2))
      | .seq p3 p4 =>
          match destIf p4 with
          | some (cmp, lhs, rhs, br1, br2) => some (.ite cmp lhs rhs (.seq (.seq br1 interm) p2) (.seq (.seq br2 interm) p2))
          | none => hoistIte2 n p3 (.seq p4 interm) dummy p2
      | _ => none

theorem hoistOk2_of (c : Compiler.Encoders.Asm.AsmConfigExact 64) (h : WordLangProgHOL (BitVec 64) → Nat) :
    ∀ (n : Nat) (p1 interm dummy p2 : WordLangProgHOL (BitVec 64)),
      (∀ H, hoistIte2 n p1 interm dummy p2 = some H → CfOk c h H .ln) → HoistOk2 c h n p1 interm dummy p2
  | 0, _, _, _, _, _ => by simp only [HoistOk2]
  | n + 1, p1, interm, dummy, p2, hk => by
      cases p1 <;> simp only [HoistOk2] <;> try trivial
      case ite cmp lhs rhs br1 br2 => exact hk _ (by simp [hoistIte2])
      case seq p3 p4 =>
        rcases hd : destIf p4 with _ | ⟨cmp, lhs, rhs, br1, br2⟩
        · simp only
          exact hoistOk2_of c h n p3 _ dummy p2 (fun H hH => hk H (by simp [hoistIte2, hd, hH]))
        · simp only
          exact hk _ (by simp [hoistIte2, hd])

def hoistIte1 (p1 p2 : WordLangProgHOL (BitVec 64)) : Option (WordLangProgHOL (BitVec 64)) :=
  match destIf p2 with
  | none => none
  | some (cmp, lhs, rhs, _, _) => hoistIte2 rewriteDuplicateIfMaxReassoc p1 .skip (.ite cmp lhs rhs (.raise 1) (.raise 2)) p2

theorem hoistOk1_of (c : Compiler.Encoders.Asm.AsmConfigExact 64) (h : WordLangProgHOL (BitVec 64) → Nat)
    (p1 p2 : WordLangProgHOL (BitVec 64)) (hk : ∀ H, hoistIte1 p1 p2 = some H → CfOk c h H .ln) :
    HoistOk1 c h p1 p2 := by
  simp only [HoistOk1]
  rcases hd : destIf p2 with _ | ⟨cmp, lhs, rhs, a, b⟩
  · trivial
  · simp only
    exact hoistOk2_of c h _ p1 .skip _ p2 (fun H hH => hk H (by simp [hoistIte1, hd, hH]))

/-- Kernel-checkable `SdiOk` with budget table `T`: at every successful hoist the
hoisted fold's drops `H` fit the budget, its expression rewrites are checked,
and nested hoists are checked against `T - H`. -/
noncomputable def sdiOkB (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    SiteTable → WordLangProgHOL (BitVec 64) → Bool
  | T, .mustTerminate q => sdiOkB c T q
  | _, .call none _ _ none => true
  | T, .call none _ _ (some (_, q2, _, _)) => sdiOkB c T q2
  | T, .call (some (_, _, q1, _, _)) _ _ none => sdiOkB c T q1
  | T, .call (some (_, _, q1, _, _)) _ _ (some (_, q2, _, _)) => sdiOkB c T q1 && sdiOkB c T q2
  | T, .ite _ _ _ a b => sdiOkB c T a && sdiOkB c T b
  | T, .loop _ b _ => sdiOkB c T b
  | T, .seq p1 p2 =>
      match tryIfHoist1F (sdiF p1) (sdiF p2) with
      | none => sdiOkB c T p1 && sdiOkB c T p2
      | some _ =>
          match hoistIte1 (sdiF p1) (sdiF p2) with
          | none => false
          | some Hp =>
              let H := dropTab [] Hp .ln
              leTable H T && cfOkB c H Hp .ln && sdiOkB c (tsub T H) p1 && sdiOkB c (tsub T H) p2
  | _, _ => true

theorem sdiOkB_sound (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ (T : SiteTable) (p : WordLangProgHOL (BitVec 64)), sdiOkB c T p = true → SdiOk c (surOf T) p
  | T, .mustTerminate q, h => by simp only [sdiOkB] at h; exact sdiOkB_sound c T q h
  | T, .call none _ _ none, h => by simp only [SdiOk]
  | T, .call none _ _ (some (_, q2, _, _)), h => by simp only [sdiOkB] at h; exact sdiOkB_sound c T q2 h
  | T, .call (some (_, _, q1, _, _)) _ _ none, h => by simp only [sdiOkB] at h; exact sdiOkB_sound c T q1 h
  | T, .call (some (_, _, q1, _, _)) _ _ (some (_, q2, _, _)), h => by
      simp only [sdiOkB, Bool.and_eq_true] at h; exact ⟨sdiOkB_sound c T q1 h.1, sdiOkB_sound c T q2 h.2⟩
  | T, .ite _ _ _ a b, h => by
      simp only [sdiOkB, Bool.and_eq_true] at h; exact ⟨sdiOkB_sound c T a h.1, sdiOkB_sound c T b h.2⟩
  | T, .loop _ b _, h => by simp only [sdiOkB] at h; exact sdiOkB_sound c T b h
  | T, .seq p1 p2, h => by
      simp only [sdiOkB] at h
      simp only [SdiOk, ← sdiF_eq, ← tryIfHoist1F_eq]
      split at h
      · rename_i hn; rw [hn]
        simp only [Bool.and_eq_true] at h
        exact ⟨sdiOkB_sound c T p1 h.1, sdiOkB_sound c T p2 h.2⟩
      · rename_i p3 hs; rw [hs]
        split at h
        · cases h
        rename_i Hp hHp
        simp only [Bool.and_eq_true] at h
        obtain ⟨⟨⟨hle, hcf⟩, h1⟩, h2⟩ := h
        refine ⟨surOf (dropTab [] Hp .ln), surOf (tsub T (dropTab [] Hp .ln)), surShape_surOf _, surShape_surOf _,
          fun q => ?_, ?_, ?_, ?_⟩
        · rw [surOf_tsub]; have := surOf_le hle q; omega
        · exact hoistOk1_of c _ _ _ (fun H hH => by
            rw [hHp] at hH; cases hH; exact cfOkB_sound c _ _ _ hcf)
        · exact sdiOkB_sound c _ p1 h1
        · exact sdiOkB_sound c _ p2 h2
  | T, .skip, _ | T, .move _ _, _ | T, .inst _, _ | T, .assign _ _, _ | T, .get _ _, _ | T, .set _ _, _
  | T, .store _ _, _ | T, .alloc _ _, _ | T, .storeConsts _ _ _ _ _, _ | T, .raise _, _ | T, .return _ _, _
  | T, .break _, _ | T, .continue _, _ | T, .tick, _ | T, .opCurrHeap _ _ _, _ | T, .locValue _ _, _
  | T, .install _ _ _ _ _, _ | T, .codeBufferWrite _ _, _ | T, .dataBufferWrite _ _, _
  | T, .ffi _ _ _ _ _ _, _ | T, .shareInst _ _ _, _ => by unfold SdiOk; trivial

#print axioms sdiOkB_sound
#print axioms sdiF_eq
#print axioms cfOkB_sound
#print axioms cfLoopF_eq
end InitECandidate.Runtime.FineCost
