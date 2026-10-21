import InitECandidate.Runtime.SourceCostLoopPrice
import InitECandidate.Runtime.PanSourcePriceDef
import Flapjack.Pancake.Semantics.PanProps
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-- Variable information a `pan_to_crep` context gives prices: shape and slot count. -/
def contextInfo (context : PanToCrepContextExact 64) (name : MlStringHOL) :
    Option (ShapeHOL × Nat) :=
  (context.vars.lookup name).map (fun entry => (entry.1, entry.2.length))

theorem loadPrices_eq (K : NodeK) (p : CrepExpHOL 64) :
    ∀ (count : Nat) (offset : BitVec 64),
      (loadShapeBytesHOLW offset count p).map (nodePriceK K) = loadPrices K (nodePriceK K p) offset count
  | 0, _ => by simp [loadShapeBytesHOLW, loadPrices]
  | count + 1, offset => by
    simp only [loadShapeBytesHOLW, loadPrices, List.map_cons, loadPrices_eq K p count]
    congr 1
    split <;> simp_all [nodePriceK, nodePriceListK] <;> omega

theorem fieldPrices_eq (K : NodeK) : ∀ (index : Nat) (shapes : List ShapeHOL) (es : List (CrepExpHOL 64)),
    ((compFieldHOL index shapes es).1.map (nodePriceK K), (compFieldHOL index shapes es).2) =
      fieldPrices K index shapes (es.map (nodePriceK K))
  | _, [], _ => by simp [compFieldHOL, fieldPrices, nodePriceK]
  | index, shape :: shapes, es => by
    rw [compFieldHOL, fieldPrices]
    split
    · simp [List.map_take]
    · rw [← List.map_drop]; exact fieldPrices_eq K (index - 1) shapes _

theorem cexpHeads_map {α β : Type} (f : α → β) : ∀ ls : List (List α),
    cexpHeads (ls.map (List.map f)) = (cexpHeads ls).map (List.map f)
  | [] => by simp [cexpHeads]
  | l :: ls => by
    have ih := cexpHeads_map f ls
    cases l with
    | nil => simp [cexpHeads]
    | cons a as =>
      simp only [List.map_cons, cexpHeads, ih]
      cases cexpHeads ls <;> simp

theorem map_var_prices (K : NodeK) (names : List Nat) :
    names.map (fun name => nodePriceK K (CrepExpHOL.var (width := 64) name)) =
      List.replicate names.length K.var := by
  induction names with
  | nil => rfl
  | cons _ names ih =>
    rw [List.map_cons, ih, List.length_cons, List.replicate_succ]; simp [nodePriceK]

theorem nodePriceListK_eq_sum (K : NodeK) : ∀ es : List (CrepExpHOL 64),
    nodePriceListK K es = (es.map (nodePriceK K)).sum
  | [] => by simp [nodePriceListK]
  | e :: es => by simp [nodePriceListK, nodePriceListK_eq_sum K es]

theorem loopPriceList_eq_sum : ∀ es : List (CrepExpHOL 64), loopPriceList es = (es.map loopNodePrice).sum
  | [] => by simp [loopPriceList]
  | e :: es => by simp [loopPriceList, loopPriceList_eq_sum es]

mutual
  /-- The price mirror is exact: under the context's own variable information
  (and no global information, as `pan_to_crep` runs after `pan_globals`), the
  prices are the native Loop prices of the compiled words, with the same shape. -/
  theorem exprPrices_compile (K : NodeK) (context : PanToCrepContextExact 64) :
      ∀ e : ExpHOL 64,
        exprPrices K (contextInfo context) (fun _ => none) e =
          ((compileExpExactHOLW context e).1.map (nodePriceK K), (compileExpExactHOLW context e).2)
    | .const _ => by simp [exprPrices, compileExpExactHOLW, nodePriceK]
    | .var .local name => by
      simp only [exprPrices, compileExpExactHOLW, contextInfo]
      cases context.vars.lookup name with
      | none => simp [nodePriceK]
      | some entry =>
        obtain ⟨shape, names⟩ := entry
        simp [Function.comp_def, map_var_prices K]
    | .var .global _ => by simp [exprPrices, compileExpExactHOLW, nodePriceK]
    | .rstruct fields => by
      have ih := exprListPrices_compile K context fields
      simp only [exprPrices, compileExpExactHOLW, ih, List.map_map, Function.comp_def,
        List.flatMap_map, List.map_flatMap]
    | .rfield index record => by
      have ih := exprPrices_compile K context record
      rw [exprPrices, compileExpExactHOLW, ih]
      rcases compileExpExactHOLW context record with ⟨es, sh⟩
      cases sh with
      | comb shapes => exact (fieldPrices_eq K _ _ _).symm
      | _ => simp [nodePriceK]
    | .nstruct _ _ => by simp [exprPrices, compileExpExactHOLW, nodePriceK]
    | .nfield _ _ => by simp [exprPrices, compileExpExactHOLW, nodePriceK]
    | .load shape address => by
      have ih := exprPrices_compile K context address
      rw [exprPrices, compileExpExactHOLW, ih]
      rcases compileExpExactHOLW context address with ⟨_ | ⟨p, ps⟩, sh⟩
      · simp [nodePriceK]
      · simp [loadPrices_eq K]
    | .load32 address => by
      have ih := exprPrices_compile K context address
      rw [exprPrices, compileExpExactHOLW, ih]
      rcases compileExpExactHOLW context address with ⟨_ | ⟨p, ps⟩, sh⟩
      · simp [nodePriceK]
      · cases sh <;> simp [nodePriceK]
    | .loadByte address => by
      have ih := exprPrices_compile K context address
      rw [exprPrices, compileExpExactHOLW, ih]
      rcases compileExpExactHOLW context address with ⟨_ | ⟨p, ps⟩, sh⟩
      · simp [nodePriceK]
      · cases sh <;> simp [nodePriceK]
    | .op operator arguments => by
      have ih := exprListPrices_compile K context arguments
      rw [exprPrices, compileExpExactHOLW, ih]
      have heads := cexpHeads_map (nodePriceK K)
        ((compileExpExactHOLWList context arguments).map Prod.fst)
      simp only [List.map_map, Function.comp_def] at heads ⊢
      rw [heads]
      cases cexpHeads ((compileExpExactHOLWList context arguments).map Prod.fst) with
      | none => simp [nodePriceK]
      | some hs => simp [nodePriceK, nodePriceListK_eq_sum K]
    | .panop operator arguments => by
      have ih := exprListPrices_compile K context arguments
      rw [exprPrices, compileExpExactHOLW, ih]
      have heads := cexpHeads_map (nodePriceK K)
        ((compileExpExactHOLWList context arguments).map Prod.fst)
      simp only [List.map_map, Function.comp_def] at heads ⊢
      rw [heads]
      cases cexpHeads ((compileExpExactHOLWList context arguments).map Prod.fst) with
      | none => simp [nodePriceK]
      | some hs => simp [nodePriceK, nodePriceListK_eq_sum K]
    | .cmp operator left right => by
      have il := exprPrices_compile K context left
      have ir := exprPrices_compile K context right
      rw [exprPrices, compileExpExactHOLW, il, ir]
      rcases compileExpExactHOLW context left with ⟨_ | ⟨a, as⟩, sa⟩ <;>
        rcases compileExpExactHOLW context right with ⟨_ | ⟨b, bs⟩, sb⟩ <;>
        simp [nodePriceK]
    | .shift operator left right => by
      have il := exprPrices_compile K context left
      have ir := exprPrices_compile K context right
      rw [exprPrices, compileExpExactHOLW, il, ir]
      rcases compileExpExactHOLW context left with ⟨_ | ⟨a, as⟩, sa⟩ <;>
        rcases compileExpExactHOLW context right with ⟨_ | ⟨b, bs⟩, sb⟩ <;>
        simp [nodePriceK]
    | .baseAddr => by simp [exprPrices, compileExpExactHOLW, nodePriceK]
    | .topAddr => by simp [exprPrices, compileExpExactHOLW, nodePriceK]
    | .bytesInWord => by simp [exprPrices, compileExpExactHOLW, nodePriceK]
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem exprListPrices_compile (K : NodeK) (context : PanToCrepContextExact 64) :
      ∀ es : List (ExpHOL 64),
        exprListPrices K (contextInfo context) (fun _ => none) es =
          (compileExpExactHOLWList context es).map
            (fun compiled => (compiled.1.map (nodePriceK K), compiled.2))
    | [] => by simp [exprListPrices, compileExpExactHOLWList]
    | e :: es => by
      simp only [exprListPrices, compileExpExactHOLWList, List.map_cons,
        exprPrices_compile K context e, exprListPrices_compile K context es]
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end


mutual
  /-- Prices depend on local variable information only through the variables read. -/
  theorem exprPrices_congr_local (K : NodeK) (L1 L2 G : MlStringHOL → Option (ShapeHOL × Nat)) :
      ∀ e : ExpHOL 64, (∀ name ∈ varExpHOL e, L1 name = L2 name) →
        exprPrices K L1 G e = exprPrices K L2 G e
    | .const _, _ => by simp [exprPrices]
    | .var .local name, agree => by
      simp only [exprPrices, agree name (by simp [varExpHOL])]
    | .var .global _, _ => by simp [exprPrices]
    | .rstruct fields, agree => by
      have := exprListPrices_congr_local K L1 L2 G fields (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [exprPrices, this]
    | .rfield _ record, agree => by
      have := exprPrices_congr_local K L1 L2 G record (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [exprPrices, this]
    | .nstruct _ _, _ => by simp [exprPrices]
    | .nfield _ _, _ => by simp [exprPrices]
    | .load _ address, agree => by
      have := exprPrices_congr_local K L1 L2 G address (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [exprPrices, this]
    | .load32 address, agree => by
      have := exprPrices_congr_local K L1 L2 G address (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [exprPrices, this]
    | .loadByte address, agree => by
      have := exprPrices_congr_local K L1 L2 G address (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [exprPrices, this]
    | .op _ arguments, agree => by
      have := exprListPrices_congr_local K L1 L2 G arguments (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [exprPrices, this]
    | .panop _ arguments, agree => by
      have := exprListPrices_congr_local K L1 L2 G arguments (by
        intro name member; exact agree name (by simpa [varExpHOL] using member))
      simp only [exprPrices, this]
    | .cmp _ left right, agree => by
      have hl := exprPrices_congr_local K L1 L2 G left (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      have hr := exprPrices_congr_local K L1 L2 G right (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      simp only [exprPrices, hl, hr]
    | .shift _ left right, agree => by
      have hl := exprPrices_congr_local K L1 L2 G left (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      have hr := exprPrices_congr_local K L1 L2 G right (by
        intro name member; exact agree name (by simp [varExpHOL, member]))
      simp only [exprPrices, hl, hr]
    | .baseAddr, _ => by simp [exprPrices]
    | .topAddr, _ => by simp [exprPrices]
    | .bytesInWord, _ => by simp [exprPrices]
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem exprListPrices_congr_local (K : NodeK) (L1 L2 G : MlStringHOL → Option (ShapeHOL × Nat)) :
      ∀ es : List (ExpHOL 64), (∀ name ∈ (es.map varExpHOL).flatten, L1 name = L2 name) →
        exprListPrices K L1 G es = exprListPrices K L2 G es
    | [], _ => by simp [exprListPrices]
    | e :: es, agree => by
      have h1 := exprPrices_congr_local K L1 L2 G e (by
        intro name member; exact agree name (by simp [member]))
      have h2 := exprListPrices_congr_local K L1 L2 G es (by
        intro name member; exact agree name (by
          simp only [List.map_cons, List.flatten_cons, List.mem_append]; exact Or.inr member))
      simp only [exprListPrices, h1, h2]
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem everyList_mem {P : ExpHOL 64 → Bool} :
    ∀ {es : List (ExpHOL 64)}, everyExpListHOL P es = true → ∀ e ∈ es, everyExpHOL P e = true
  | [], _, _, he => by simp at he
  | x :: xs, h, e, he => by
    simp only [everyExpListHOL, Bool.and_eq_true] at h
    rcases List.mem_cons.1 he with rfl | he
    · exact h.1
    · exact everyList_mem h.2 e he

mutual
  /-- Global variable information is irrelevant for expressions without global reads. -/
  theorem exprPrices_localised (K : NodeK) (L G1 G2 : MlStringHOL → Option (ShapeHOL × Nat)) :
      ∀ e : ExpHOL 64, localisedExpHOL e = true → exprPrices K L G1 e = exprPrices K L G2 e
    | .const _, _ => by simp [exprPrices]
    | .var .local _, _ => by simp [exprPrices]
    | .var .global _, h => by simp [localisedExpHOL, everyExpHOL] at h
    | .rstruct fields, h => by
      simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h
      have := exprListPrices_localised K L G1 G2 fields (fun x hx => everyList_mem h.2 x hx)
      simp only [exprPrices, this]
    | .rfield _ record, h => by
      have := exprPrices_localised K L G1 G2 record (by
        simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h; exact h.2)
      simp only [exprPrices, this]
    | .nstruct _ _, _ => by simp [exprPrices]
    | .nfield _ _, _ => by simp [exprPrices]
    | .load _ address, h => by
      have := exprPrices_localised K L G1 G2 address (by
        simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h; exact h.2)
      simp only [exprPrices, this]
    | .load32 address, h => by
      have := exprPrices_localised K L G1 G2 address (by
        simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h; exact h.2)
      simp only [exprPrices, this]
    | .loadByte address, h => by
      have := exprPrices_localised K L G1 G2 address (by
        simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h; exact h.2)
      simp only [exprPrices, this]
    | .op _ arguments, h => by
      simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h
      have := exprListPrices_localised K L G1 G2 arguments (fun x hx => everyList_mem h.2 x hx)
      simp only [exprPrices, this]
    | .panop _ arguments, h => by
      simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h
      have := exprListPrices_localised K L G1 G2 arguments (fun x hx => everyList_mem h.2 x hx)
      simp only [exprPrices, this]
    | .cmp _ left right, h => by
      simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h
      have hl := exprPrices_localised K L G1 G2 left h.1.2
      have hr := exprPrices_localised K L G1 G2 right h.2
      simp only [exprPrices, hl, hr]
    | .shift _ left right, h => by
      simp only [localisedExpHOL, everyExpHOL, Bool.and_eq_true] at h
      have hl := exprPrices_localised K L G1 G2 left h.1.2
      have hr := exprPrices_localised K L G1 G2 right h.2
      simp only [exprPrices, hl, hr]
    | .baseAddr, _ => by simp [exprPrices]
    | .topAddr, _ => by simp [exprPrices]
    | .bytesInWord, _ => by simp [exprPrices]
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem exprListPrices_localised (K : NodeK) (L G1 G2 : MlStringHOL → Option (ShapeHOL × Nat)) :
      ∀ es : List (ExpHOL 64), (∀ e ∈ es, localisedExpHOL e = true) →
        exprListPrices K L G1 es = exprListPrices K L G2 es
    | [], _ => by simp [exprListPrices]
    | e :: es, h => by
      have h1 := exprPrices_localised K L G1 G2 e (h e (by simp))
      have h2 := exprListPrices_localised K L G1 G2 es (fun x hx => h x (by simp [hx]))
      simp only [exprListPrices, h1, h2]
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

mutual
  theorem nodePriceK_loopK : ∀ e : CrepExpHOL 64, nodePriceK loopK e = loopNodePrice e
    | .const _ | .var _ | .loadGlob _ | .baseAddr | .topAddr => by simp [nodePriceK, loopNodePrice]
    | .load a | .load32 a | .loadByte a => by simp [nodePriceK, loopNodePrice, nodePriceK_loopK a]
    | .op _ args | .crepOp _ args => by simp [nodePriceK, loopNodePrice, nodePriceListK_loopK args, Nat.add_assoc]
    | .shift _ l r | .cmp _ l r => by simp [nodePriceK, loopNodePrice, nodePriceK_loopK l, nodePriceK_loopK r]
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem nodePriceListK_loopK : ∀ es : List (CrepExpHOL 64), nodePriceListK loopK es = loopPriceList es
    | [] => by simp [nodePriceListK, loopPriceList]
    | e :: es => by simp [nodePriceListK, loopPriceList, nodePriceK_loopK e, nodePriceListK_loopK es]
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

/-- Node costs pointwise at most others give prices at most the others. -/
structure NodeK.Le (A B : NodeK) : Prop where
  cst : A.cst ≤ B.cst
  var : A.var ≤ B.var
  top : A.top ≤ B.top
  load : A.load ≤ B.load
  ld32 : A.ld32 ≤ B.ld32
  op : ∀ n, A.op n ≤ B.op n
  crepOp : A.crepOp ≤ B.crepOp
  shift : A.shift ≤ B.shift
  cmp : A.cmp ≤ B.cmp

mutual
  theorem nodePriceK_mono {A B : NodeK} (h : NodeK.Le A B) : ∀ e : CrepExpHOL 64, nodePriceK A e ≤ nodePriceK B e
    | .const _ => by simp only [nodePriceK]; exact h.cst
    | .var _ | .loadGlob _ | .baseAddr => by simp only [nodePriceK]; exact h.var
    | .topAddr => by simp only [nodePriceK]; exact h.top
    | .load a => by have := nodePriceK_mono h a; have := h.load; simp only [nodePriceK]; omega
    | .load32 a | .loadByte a => by have := nodePriceK_mono h a; have := h.ld32; simp only [nodePriceK]; omega
    | .op _ args => by
      have := nodePriceListK_mono h args; have := h.op args.length; simp only [nodePriceK]; omega
    | .crepOp _ args => by have := nodePriceListK_mono h args; have := h.crepOp; simp only [nodePriceK]; omega
    | .shift _ l r => by
      have := nodePriceK_mono h l; have := nodePriceK_mono h r; have := h.shift; simp only [nodePriceK]; omega
    | .cmp _ l r => by
      have := nodePriceK_mono h l; have := nodePriceK_mono h r; have := h.cmp; simp only [nodePriceK]; omega
  termination_by e => sizeOf e
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial

  theorem nodePriceListK_mono {A B : NodeK} (h : NodeK.Le A B) :
      ∀ es : List (CrepExpHOL 64), nodePriceListK A es ≤ nodePriceListK B es
    | [] => by simp [nodePriceListK]
    | e :: es => by
      have := nodePriceK_mono h e; have := nodePriceListK_mono h es; simp only [nodePriceListK]; omega
  termination_by es => sizeOf es
  decreasing_by all_goals first | sizeOf_list_dec | decreasing_trivial
end

theorem loopK_le_srcK : NodeK.Le loopK srcK :=
  ⟨by simp, by simp, by simp, by simp, by simp, fun n => by simp only [loopK_op, srcK_op]; omega,
    by simp, by simp, by simp⟩

theorem selK_le_srcK : NodeK.Le selK srcK :=
  ⟨by simp, by simp, by simp, by simp, by simp, fun n => by simp only [selK_op, srcK_op]; omega,
    by simp, by simp, by simp⟩

#print axioms nodePriceK_loopK
#print axioms nodePriceK_mono
#print axioms exprPrices_compile
#print axioms exprPrices_congr_local
#print axioms exprPrices_localised
end InitECandidate.Runtime.FineCost
