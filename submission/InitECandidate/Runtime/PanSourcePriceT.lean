import InitECandidate.Runtime.CrepErase
import InitECandidate.Runtime.PanSourcePriceState
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Source mirror of the pattern-aware selector price. The price of a Crep
expression is `tightP c e = max (nodeT c e) (nodeT c (simp_exp e))`: it
dominates `nodeT`, and `simp_exp` never increases it (`simp_exp` is
idempotent). The source charge of an expression compiles it under the
canonical context of the source locals and prices the words at `tightP`;
`pan_to_crep` under any related context emits the same words up to variable
numbering, so the charge is exact. -/

/-- The pattern-aware price, closed under `simp_exp`. -/
def tightP (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) : Nat :=
  max (nodeT c e) (nodeT c (crepSimpExpHOL e))

theorem nodeT_le_tightP (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) :
    nodeT c e ≤ tightP c e := Nat.le_max_left _ _

theorem tightP_simp (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) :
    tightP c (crepSimpExpHOL e) ≤ tightP c e := by
  unfold tightP; rw [crepSimp_idem, Nat.max_self]; exact Nat.le_max_right _ _

theorem tightP_erase (c : Compiler.Encoders.Asm.AsmConfigExact 64) (e : CrepExpHOL 64) :
    tightP c (crepErase e) = tightP c e := by
  unfold tightP; rw [crepSimp_erase, nodeT_erase, nodeT_erase]

/-- The compiler context of a source local map: each local's shape, with
placeholder slots of its word count. -/
def canonCtx (L : HolFiniteMapExact MlStringHOL (ValueHOL 64)) : PanToCrepContextExact 64 where
  vars := L.map2 (fun entry => (shapeOfHOLExact entry.2, List.replicate (flattenHOL entry.2).length 0))
  funcs := HolFiniteMapExact.empty
  eids := HolFiniteMapExact.empty
  vmax := 0

theorem contextInfo_canonCtx (L : HolFiniteMapExact MlStringHOL (ValueHOL 64)) (name : MlStringHOL) :
    contextInfo (canonCtx L) name = valueInfo L name := by
  simp only [contextInfo, canonCtx, HolFiniteMapExact.lookup_map2, valueInfo, Option.map_map]
  cases L.lookup name <;> simp

theorem loadShapeBytes_erase : ∀ (count : Nat) (offset : BitVec 64) (p : CrepExpHOL 64),
    (loadShapeBytesHOLW offset count p).map crepErase = loadShapeBytesHOLW offset count (crepErase p)
  | 0, _, _ => by simp [loadShapeBytesHOLW]
  | count + 1, offset, p => by
    simp only [loadShapeBytesHOLW, List.map_cons, loadShapeBytes_erase count]
    congr 1
    split <;> simp

theorem compField_erase : ∀ (index : Nat) (shapes : List ShapeHOL) (es : List (CrepExpHOL 64)),
    compFieldHOL index shapes (es.map crepErase) =
      ((compFieldHOL index shapes es).1.map crepErase, (compFieldHOL index shapes es).2)
  | _, [], _ => by simp [compFieldHOL]
  | index, shape :: shapes, es => by
    rw [compFieldHOL, compFieldHOL]
    split
    · simp [List.map_take]
    · rw [← List.map_drop]; exact compField_erase (index - 1) shapes _

/-- Erased compiled words and shape. -/
def erasedCompile (context : PanToCrepContextExact 64) (e : ExpHOL 64) : List (CrepExpHOL 64) × ShapeHOL :=
  ((compileExpExactHOLW context e).1.map crepErase, (compileExpExactHOLW context e).2)

mutual
  /-- Contexts that agree on the information of the variables an expression
  reads compile it to the same words up to variable numbering. -/
  theorem compile_erase_congr (c1 c2 : PanToCrepContextExact 64) :
      ∀ e : ExpHOL 64, (∀ name ∈ varExpHOL e, contextInfo c1 name = contextInfo c2 name) →
        erasedCompile c1 e = erasedCompile c2 e
    | .const _, _ => by simp [erasedCompile, compileExpExactHOLW]
    | .var .local name, agree => by
      have h := agree name (by simp [varExpHOL])
      simp only [contextInfo] at h
      simp only [erasedCompile, compileExpExactHOLW]
      cases h1 : c1.vars.lookup name with
      | none =>
        cases h2 : c2.vars.lookup name with
        | none => rfl
        | some e2 => rw [h1, h2] at h; simp at h
      | some e1 =>
        cases h2 : c2.vars.lookup name with
        | none => rw [h1, h2] at h; simp at h
        | some e2 =>
          rw [h1, h2] at h
          obtain ⟨s1, n1⟩ := e1; obtain ⟨s2, n2⟩ := e2
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, hl⟩ := h
          simp only [List.map_map, Function.comp_def, crepErase_var, Prod.mk.injEq, and_true]
          rw [List.map_const', List.map_const', hl]
    | .var .global _, _ => by simp [erasedCompile, compileExpExactHOLW]
    | .rstruct fields, agree => by
      have ih := compileList_erase_congr c1 c2 fields (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [erasedCompile, compileExpExactHOLW, List.map_flatMap] at ih ⊢
      have h1 : (compileExpExactHOLWList c1 fields).flatMap (fun a => a.1.map crepErase) =
          ((compileExpExactHOLWList c1 fields).map (fun x => (x.1.map crepErase, x.2))).flatMap Prod.fst := by
        simp [List.flatMap_map]
      have h2 : (compileExpExactHOLWList c2 fields).flatMap (fun a => a.1.map crepErase) =
          ((compileExpExactHOLWList c2 fields).map (fun x => (x.1.map crepErase, x.2))).flatMap Prod.fst := by
        simp [List.flatMap_map]
      have s1 : (compileExpExactHOLWList c1 fields).map Prod.snd =
          ((compileExpExactHOLWList c1 fields).map (fun x => (x.1.map crepErase, x.2))).map Prod.snd := by
        simp
      have s2 : (compileExpExactHOLWList c2 fields).map Prod.snd =
          ((compileExpExactHOLWList c2 fields).map (fun x => (x.1.map crepErase, x.2))).map Prod.snd := by
        simp
      rw [h1, h2, s1, s2, ih]
    | .rfield index record, agree => by
      have ih := compile_erase_congr c1 c2 record (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [erasedCompile, Prod.mk.injEq] at ih
      simp only [erasedCompile, compileExpExactHOLW]
      rcases hc1 : compileExpExactHOLW c1 record with ⟨es1, sh1⟩
      rcases hc2 : compileExpExactHOLW c2 record with ⟨es2, sh2⟩
      rw [hc1, hc2] at ih
      obtain ⟨he, rfl⟩ := ih
      simp only []
      cases sh1 with
      | comb shapes =>
        have k1 := compField_erase index shapes es1
        have k2 := compField_erase index shapes es2
        rw [he] at k1
        rw [k1] at k2
        exact k2.symm ▸ rfl
      | _ => rfl
    | .nstruct _ _, _ => by simp [erasedCompile, compileExpExactHOLW]
    | .nfield _ _, _ => by simp [erasedCompile, compileExpExactHOLW]
    | .load shape address, agree => by
      have ih := compile_erase_congr c1 c2 address (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [erasedCompile, Prod.mk.injEq] at ih
      simp only [erasedCompile, compileExpExactHOLW]
      generalize compileExpExactHOLW c1 address = r1 at ih ⊢
      generalize compileExpExactHOLW c2 address = r2 at ih ⊢
      obtain ⟨es1, sh1⟩ := r1; obtain ⟨es2, sh2⟩ := r2
      simp only [] at ih
      obtain ⟨he, rfl⟩ := ih
      cases es1 with
      | nil => cases es2 with
        | nil => rfl
        | cons _ _ => simp at he
      | cons p1 ps1 => cases es2 with
        | nil => simp at he
        | cons p2 ps2 =>
          simp only [List.map_cons, List.cons.injEq] at he
          simp only [loadShapeBytes_erase, he.1]
    | .load32 address, agree => by
      have ih := compile_erase_congr c1 c2 address (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [erasedCompile, Prod.mk.injEq] at ih
      simp only [erasedCompile, compileExpExactHOLW]
      generalize compileExpExactHOLW c1 address = r1 at ih ⊢
      generalize compileExpExactHOLW c2 address = r2 at ih ⊢
      obtain ⟨es1, sh1⟩ := r1; obtain ⟨es2, sh2⟩ := r2
      simp only [] at ih
      obtain ⟨he, rfl⟩ := ih
      cases es1 with
      | nil => cases es2 with
        | nil => rfl
        | cons _ _ => simp at he
      | cons p1 ps1 => cases es2 with
        | nil => simp at he
        | cons p2 ps2 =>
          simp only [List.map_cons, List.cons.injEq] at he
          cases sh1 <;> simp [he.1]
    | .loadByte address, agree => by
      have ih := compile_erase_congr c1 c2 address (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [erasedCompile, Prod.mk.injEq] at ih
      simp only [erasedCompile, compileExpExactHOLW]
      generalize compileExpExactHOLW c1 address = r1 at ih ⊢
      generalize compileExpExactHOLW c2 address = r2 at ih ⊢
      obtain ⟨es1, sh1⟩ := r1; obtain ⟨es2, sh2⟩ := r2
      simp only [] at ih
      obtain ⟨he, rfl⟩ := ih
      cases es1 with
      | nil => cases es2 with
        | nil => rfl
        | cons _ _ => simp at he
      | cons p1 ps1 => cases es2 with
        | nil => simp at he
        | cons p2 ps2 =>
          simp only [List.map_cons, List.cons.injEq] at he
          cases sh1 <;> simp [he.1]
    | .op operator arguments, agree => by
      have ih := compileList_erase_congr c1 c2 arguments (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      have hm : ∀ c : PanToCrepContextExact 64, ((compileExpExactHOLWList c arguments).map Prod.fst).map
          (List.map crepErase) = ((compileExpExactHOLWList c arguments).map
            (fun x => (x.1.map crepErase, x.2))).map Prod.fst := by intro c; simp
      have key : (cexpHeads ((compileExpExactHOLWList c1 arguments).map Prod.fst)).map (List.map crepErase) =
          (cexpHeads ((compileExpExactHOLWList c2 arguments).map Prod.fst)).map (List.map crepErase) := by
        rw [← cexpHeads_map, ← cexpHeads_map, hm c1, hm c2, ih]
      simp only [erasedCompile, compileExpExactHOLW]
      generalize cexpHeads ((compileExpExactHOLWList c1 arguments).map Prod.fst) = h1 at key ⊢
      generalize cexpHeads ((compileExpExactHOLWList c2 arguments).map Prod.fst) = h2 at key ⊢
      cases h1 with
      | none => cases h2 with
        | none => rfl
        | some _ => simp at key
      | some hs1 => cases h2 with
        | none => simp at key
        | some hs2 =>
          simp only [Option.map_some, Option.some.injEq] at key
          simp [key]
    | .panop operator arguments, agree => by
      have ih := compileList_erase_congr c1 c2 arguments (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      have hm : ∀ c : PanToCrepContextExact 64, ((compileExpExactHOLWList c arguments).map Prod.fst).map
          (List.map crepErase) = ((compileExpExactHOLWList c arguments).map
            (fun x => (x.1.map crepErase, x.2))).map Prod.fst := by intro c; simp
      have key : (cexpHeads ((compileExpExactHOLWList c1 arguments).map Prod.fst)).map (List.map crepErase) =
          (cexpHeads ((compileExpExactHOLWList c2 arguments).map Prod.fst)).map (List.map crepErase) := by
        rw [← cexpHeads_map, ← cexpHeads_map, hm c1, hm c2, ih]
      simp only [erasedCompile, compileExpExactHOLW]
      generalize cexpHeads ((compileExpExactHOLWList c1 arguments).map Prod.fst) = h1 at key ⊢
      generalize cexpHeads ((compileExpExactHOLWList c2 arguments).map Prod.fst) = h2 at key ⊢
      cases h1 with
      | none => cases h2 with
        | none => rfl
        | some _ => simp at key
      | some hs1 => cases h2 with
        | none => simp at key
        | some hs2 =>
          simp only [Option.map_some, Option.some.injEq] at key
          simp [key]
    | .cmp operator left right, agree => by
      have il := compile_erase_congr c1 c2 left (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      have ir := compile_erase_congr c1 c2 right (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      simp only [erasedCompile, Prod.mk.injEq] at il ir
      simp only [erasedCompile, compileExpExactHOLW]
      rcases hl1 : compileExpExactHOLW c1 left with ⟨_ | ⟨a1, as1⟩, sa1⟩ <;>
        rcases hl2 : compileExpExactHOLW c2 left with ⟨_ | ⟨a2, as2⟩, sa2⟩ <;>
        rcases hr1 : compileExpExactHOLW c1 right with ⟨_ | ⟨b1, bs1⟩, sb1⟩ <;>
        rcases hr2 : compileExpExactHOLW c2 right with ⟨_ | ⟨b2, bs2⟩, sb2⟩ <;>
        rw [hl1, hl2] at il <;> rw [hr1, hr2] at ir <;>
        simp_all
    | .shift operator left right, agree => by
      have il := compile_erase_congr c1 c2 left (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      have ir := compile_erase_congr c1 c2 right (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      simp only [erasedCompile, Prod.mk.injEq] at il ir
      simp only [erasedCompile, compileExpExactHOLW]
      rcases hl1 : compileExpExactHOLW c1 left with ⟨_ | ⟨a1, as1⟩, sa1⟩ <;>
        rcases hl2 : compileExpExactHOLW c2 left with ⟨_ | ⟨a2, as2⟩, sa2⟩ <;>
        rcases hr1 : compileExpExactHOLW c1 right with ⟨_ | ⟨b1, bs1⟩, sb1⟩ <;>
        rcases hr2 : compileExpExactHOLW c2 right with ⟨_ | ⟨b2, bs2⟩, sb2⟩ <;>
        rw [hl1, hl2] at il <;> rw [hr1, hr2] at ir <;>
        simp_all
    | .baseAddr, _ => by simp [erasedCompile, compileExpExactHOLW]
    | .topAddr, _ => by simp [erasedCompile, compileExpExactHOLW]
    | .bytesInWord, _ => by simp [erasedCompile, compileExpExactHOLW]
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem compileList_erase_congr (c1 c2 : PanToCrepContextExact 64) :
      ∀ es : List (ExpHOL 64), (∀ name ∈ (es.map varExpHOL).flatten, contextInfo c1 name = contextInfo c2 name) →
        (compileExpExactHOLWList c1 es).map (fun x => (x.1.map crepErase, x.2)) =
          (compileExpExactHOLWList c2 es).map (fun x => (x.1.map crepErase, x.2))
    | [], _ => by simp [compileExpExactHOLWList]
    | e :: es, agree => by
      have h1 := compile_erase_congr c1 c2 e (by
        intro name member; exact agree name (by simp [member]))
      have h2 := compileList_erase_congr c1 c2 es (by
        intro name member; exact agree name (by
          simp only [List.map_cons, List.flatten_cons, List.mem_append]; exact Or.inr member))
      simp only [erasedCompile] at h1
      simp only [compileExpExactHOLWList, List.map_cons, h1, h2]
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- The source charge of an expression at the pattern-aware price. -/
def sourcePriceT (c : Compiler.Encoders.Asm.AsmConfigExact 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (e : ExpHOL 64) : Nat :=
  ((compileExpExactHOLW (canonCtx s.locals) e).1.map (tightP c)).sum

theorem tightP_sum_erase (c : Compiler.Encoders.Asm.AsmConfigExact 64) (es : List (CrepExpHOL 64)) :
    ((es.map crepErase).map (tightP c)).sum = (es.map (tightP c)).sum := by
  rw [List.map_map]; congr 1; exact List.map_congr_left (fun e _ => tightP_erase c e)

/-- Exactness: `pan_to_crep` under a related context emits words whose
pattern-aware price is the source charge. -/
theorem sourcePriceT_compile (c : Compiler.Encoders.Asm.AsmConfigExact 64) {F : Type}
    (s : PanSemStateFiniteExact 64 F) (context : PanToCrepContextExact 64)
    (targetLocals : HolFiniteMapExact Nat (HolWordLab 64))
    (related : panToCrepLocalsRelFiniteExact context s.locals targetLocals)
    (e : ExpHOL 64) (value : ValueHOL 64) (evaluated : expressionValue s e = some value) :
    ((compileExpExactHOLW context e).1.map (tightP c)).sum = sourcePriceT c s e := by
  have present := expression_success_locals_present s e value evaluated
  have congr := compile_erase_congr context (canonCtx s.locals) e (fun name member => by
    obtain ⟨v, found⟩ := present name member
    rw [contextInfo_canonCtx, ← valueInfo_context related found])
  simp only [erasedCompile, Prod.mk.injEq] at congr
  rw [sourcePriceT, ← tightP_sum_erase c (compileExpExactHOLW context e).1, congr.1, tightP_sum_erase]

#print axioms sourcePriceT_compile
#print axioms tightP_simp
end InitECandidate.Runtime.FineCost
