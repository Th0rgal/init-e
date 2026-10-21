import InitECandidate.Runtime.SourceCostSharpCrepCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-! Static width bound for compiled return names: every variable of a
`pan_to_crep` context has at most 21 slots. A compiled call then names at most
21 return slots, the count the Loop call sequence moves in registers. -/

/-- Every context variable has at most 21 slots. -/
def VarsSmall (context : PanToCrepContextExact 64) : Prop :=
  ∀ name shape slots, context.vars.lookup name = some (shape, slots) → slots.length ≤ 21

theorem wrapRtHOL_some {v : Option (ShapeHOL × List Nat)} {sh : ShapeHOL} {ns : List Nat}
    (h : wrapRtHOL v = some (sh, ns)) : v = some (sh, ns) := by
  unfold wrapRtHOL at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact h


/-- Every function of a context takes parameters, and returns a value, of at most 21 words. -/
def FuncsSmall (context : PanToCrepContextExact 64) : Prop :=
  ∀ function params returnShape, context.funcs.lookup function = some (params, returnShape) →
    (∀ p ∈ params, sizeOfShapeHOL p.2 ≤ 21) ∧ sizeOfShapeHOL returnShape ≤ 21

theorem fupdate_some {α β : Type} [BEq α] [LawfulBEq α] (P : β → Prop) (m : Flapjack.FiniteMap α β)
    (entry : α × β) (hm : ∀ k v, m k = some v → P v) (he : P entry.2) :
    ∀ k v, Flapjack.FUPDATE m entry k = some v → P v := by
  intro k v h
  unfold Flapjack.FUPDATE at h
  split at h
  · cases h; exact he
  · exact hm k v h

theorem fupdateList_some {α β : Type} [BEq α] [LawfulBEq α] (P : β → Prop) :
    ∀ (entries : List (α × β)) (m : Flapjack.FiniteMap α β), (∀ k v, m k = some v → P v) →
      (∀ e ∈ entries, P e.2) → ∀ k v, Flapjack.FUPDATE_LIST m entries k = some v → P v
  | [], m, hm, _, k, v, h => hm k v (by simpa [Flapjack.FUPDATE_LIST] using h)
  | e :: es, m, hm, he, k, v, h => by
    simp only [Flapjack.FUPDATE_LIST, List.foldl_cons] at h
    exact fupdateList_some P es (Flapjack.FUPDATE m e)
      (fupdate_some P m e hm (he e (by simp))) (fun e' h' => he e' (by simp [h'])) k v
      (by simpa [Flapjack.FUPDATE_LIST] using h)

theorem withShape_zip_le : ∀ (shapes : List ShapeHOL) (ns : List Nat) (shape : ShapeHOL)
    (chunk : List Nat), (shape, chunk) ∈ shapes.zip (withShapeHOL shapes ns) →
      chunk.length ≤ sizeOfShapeHOL shape
  | [], _, _, _, h => by simp [withShapeHOL] at h
  | s :: ss, ns, shape, chunk, h => by
    simp only [withShapeHOL, List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp
    · exact withShape_zip_le ss _ shape chunk h

/-- A callee entry context built from parameter shapes of at most 21 words. -/
theorem varsSmall_ctxtFc (cvs : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ShapeHOL))
    (em : HolFiniteMapExact MlS (BitVec 64)) (vs : List MlS) (shs : List ShapeHOL) (ns : List Nat)
    (small : ∀ sh ∈ shs, sizeOfShapeHOL sh ≤ 21) :
    VarsSmall (ctxtFcExactHOL cvs em vs shs ns) := by
  intro name shape slots h
  simp only [ctxtFcExactHOL, HolFiniteMapExact.lookup_updateList] at h
  refine fupdateList_some (fun (x : ShapeHOL × List Nat) => x.2.length ≤ sizeOfShapeHOL x.1 ∧
      sizeOfShapeHOL x.1 ≤ 21) _ _ (by simp) ?_ name (shape, slots) h |> fun h => Nat.le_trans h.1 h.2
  intro e he
  obtain ⟨-, hm⟩ := List.of_mem_zip he
  have hsh := (List.of_mem_zip hm).1
  exact ⟨withShape_zip_le shs ns e.2.1 e.2.2 hm, small _ hsh⟩

/-- The DecCall/Dec continuation context keeps every variable within 21 slots. -/
theorem varsSmall_decCallCtxt {context : PanToCrepContextExact 64} (small : VarsSmall context)
    (name : MlS) {shape : ShapeHOL} (hs : sizeOfShapeHOL shape ≤ 21) :
    VarsSmall (decCallCtxt context name shape) := by
  intro k sh ns h
  simp only [decCallCtxt, HolFiniteMapExact.lookup_update] at h
  unfold Flapjack.FUPDATE at h
  split at h
  · cases h; simpa [decCallSlots] using hs
  · exact small k sh ns h

theorem funcsSmall_of_funcs {c c' : PanToCrepContextExact 64} (h : c'.funcs = c.funcs)
    (fs : FuncsSmall c) : FuncsSmall c' := by
  intro f p r hl; rw [h] at hl; exact fs f p r hl

/-- Every declared shape (`dec`, `decCall`) of a program, including handler
bodies, has at most 21 words. -/
def widthProg : ProgHOL 64 → Bool
  | .dec _ shape _ body => decide (sizeOfShapeHOL shape ≤ 21) && widthProg body
  | .decCall _ shape _ _ continuation => decide (sizeOfShapeHOL shape ≤ 21) && widthProg continuation
  | .seq first second => widthProg first && widthProg second
  | .ite _ yes no => widthProg yes && widthProg no
  | .while _ body => widthProg body
  | .call (some (_, some (_, _, handler))) _ _ => widthProg handler
  | _ => true

/-- Every body of a code table passes `widthProg`. -/
def CodeWidth (code : HolFiniteMapExact MlStringHOL
    (List (MlStringHOL × ShapeHOL) × ProgHOL 64 × ShapeHOL)) : Prop :=
  ∀ function shapes body returnShape, code.lookup function = some (shapes, body, returnShape) →
    widthProg body = true

/-- `compileCallSomeShapeHdl` with the existing-variable case bounded by `VarsSmall`. -/
theorem compileCallSomeShapeHdl_small (ctxt : PanToCrepContextExact 64)
    (dest : Option (VarKind × MlS)) (hdl : Option (MlS × MlS × ProgHOL 64))
    (f : MlS) (args : List (ExpHOL 64))
    (vshapes : List (MlS × ShapeHOL)) (rsh : ShapeHOL)
    (hno : noOverlapFiniteExact ctxt.vars) (small : VarsSmall ctxt)
    (hfuncs : ctxt.funcs.lookup f = some (vshapes, rsh)) :
    let cargs := (compileExpExactHOLWList ctxt args).flatMap Prod.fst
    let rts := (List.range (sizeOfShapeHOL rsh)).map (fun i => ctxt.vmax + i + 1)
    compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) =
        nestedDecsHOL rts (List.replicate rts.length (.const (0 : BitVec 64)))
          (.call (some (rts, compileCallHdlC ctxt hdl)) f cargs) ∨
      (compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) = .call none f cargs ∧
        compileCallHdlC ctxt hdl = none) ∨
      ∃ rts0 : List Nat, rts0.Nodup ∧ rts0.length ≤ 21 ∧
        compileProgExactHOLW ctxt (.call (some (dest, hdl)) f args) =
          .call (some (rts0, compileCallHdlC ctxt hdl)) f cargs := by
  intro cargs rts
  rcases dest with _ | ⟨kind, name⟩ <;> rcases hdl with _ | ⟨eid, evar, p⟩ <;>
    simp only [compileProgExactHOLW]
  · exact Or.inl (by simp [compileCallResultNoHandlerExactHOLW, hfuncs, cargs, rts, compileCallHdlC])
  · split
    · rename_i hE
      exact Or.inl (by simp [compileCallHandlerMissingEidExactHOLW,
        compileCallResultNoHandlerExactHOLW, hfuncs, cargs, rts, compileCallHdlC, hE])
    · rename_i code hE
      exact Or.inl (by simp [compileCallHandlerPresentEidExactHOLW, hfuncs, cargs, rts,
        compileCallHdlC, hE])
  · split
    · exact Or.inr (Or.inl ⟨by simp [compileCallWrappedResultFallbackNoHandlerExactHOLW, cargs],
        rfl⟩)
    · rename_i sh ns hwrap
      refine Or.inr (Or.inr ⟨ns, noOverlapWrapRtSomeAllDistinctFiniteExact ctxt.vars name sh ns
        hno hwrap, small name sh ns (wrapRtHOL_some hwrap),
        by simp [compileCallWrappedResultNoHandlerExactHOLW, cargs, compileCallHdlC]⟩)
  · split
    · split
      · rename_i hE
        exact Or.inr (Or.inl ⟨by simp [compileCallWrappedResultFallbackHandlerMissingEidExactHOLW,
            compileCallWrappedResultFallbackNoHandlerExactHOLW, cargs],
          by simp [compileCallHdlC, hE]⟩)
      · rename_i code hE
        refine Or.inr (Or.inr ⟨[], List.nodup_nil, by simp, ?_⟩)
        simp [compileCallWrappedResultFallbackHandlerPresentEidExactHOLW, cargs, compileCallHdlC, hE]
    · rename_i sh ns hwrap
      have hns := noOverlapWrapRtSomeAllDistinctFiniteExact ctxt.vars name sh ns hno hwrap
      have hlen := small name sh ns (wrapRtHOL_some hwrap)
      split
      · rename_i hE
        refine Or.inr (Or.inr ⟨ns, hns, hlen, ?_⟩)
        simp [compileCallWrappedResultHandlerMissingEidExactHOLW,
          compileCallWrappedResultNoHandlerExactHOLW, cargs, compileCallHdlC, hE]
      · rename_i code hE
        refine Or.inr (Or.inr ⟨ns, hns, hlen, ?_⟩)
        simp [compileCallWrappedResultHandlerPresentEidExactHOLW, cargs, compileCallHdlC, hE]

#print axioms compileCallSomeShapeHdl_small
#print axioms varsSmall_ctxtFc
#print axioms varsSmall_decCallCtxt
end InitECandidate.Runtime.FineCost
