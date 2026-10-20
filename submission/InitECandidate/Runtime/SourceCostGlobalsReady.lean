import InitECandidate.Runtime.SourceCostGlobalsInvariant
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-! Program certificate for the `pan_globals` run transfer, and the run
invariant that no local is named like the `pan_globals` call temporary. -/

/-- The local `pan_globals` declares for a call result stored into a global. -/
def globalsTemp : MlS := Flapjack.Basis.Pure.MlString.ofString ""

/-- Programs whose `pan_globals` expansion is paid by `globalAccess` events:
ready expressions, no handled call into a global, no shared load into a
global, and no declaration named like the call temporary. -/
def globalsReadyProg : ProgHOL 64 → Bool
  | .dec name _ e body => name != globalsTemp && globalsReadyExp e && globalsReadyProg body
  | .assign _ _ e | .return e | .raise _ e => globalsReadyExp e
  | .primitive _ _ es => globalsReadyExps es
  | .store a b | .store32 a b | .storeByte a b | .shMemStore _ a b =>
      globalsReadyExp a && globalsReadyExp b
  | .seq a b => globalsReadyProg a && globalsReadyProg b
  | .ite e a b => globalsReadyExp e && globalsReadyProg a && globalsReadyProg b
  | .while e body => globalsReadyExp e && globalsReadyProg body
  | .call (some (some (.global, _), some _)) _ _ => false
  | .call (some (_, some (_, _, handler))) _ es => globalsReadyExps es && globalsReadyProg handler
  | .call _ _ es => globalsReadyExps es
  | .decCall name _ _ es body => name != globalsTemp && globalsReadyExps es && globalsReadyProg body
  | .extCall _ a b c d => globalsReadyExp a && globalsReadyExp b && globalsReadyExp c && globalsReadyExp d
  | .shMemLoad _ .global _ _ => false
  | .shMemLoad _ .local _ e => globalsReadyExp e
  | _ => true
termination_by p => sizeOf p

/-- Every installed function body is ready and no parameter is named like the
call temporary. -/
def GlobalsCodeReady (code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :
    Prop :=
  ∀ function parameters body returnShape,
    code.lookup function = some (parameters, body, returnShape) →
      globalsReadyProg body = true ∧ globalsTemp ∉ parameters.map Prod.fst

theorem globals_foldl_absent {β : Type} (key : MlS) :
    ∀ (entries : List (MlS × β)) (init : MlS → Option β), key ∉ entries.map Prod.fst →
      List.foldl (fun (map : MlS → Option β) (entry : MlS × β) =>
        fun current => if current = entry.1 then some entry.2 else map current) init entries key =
        init key
  | [], _, _ => rfl
  | head :: tail, init, absent => by
    simp only [List.map_cons, List.mem_cons, not_or] at absent
    rw [List.foldl_cons, globals_foldl_absent key tail _ absent.2]
    simp [absent.1]

theorem globals_callee_noTemp {code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    (ready : GlobalsCodeReady code) {function : MlS} {values : List (ValueHOL 64)} {body callee returnShape}
    (lookup : lookupCodeHOLFinite code.lookup function values = some (body, callee, returnShape)) :
    callee.lookup globalsTemp = none := by
  have exact := lookupCodeHOLFinite_eq_some code.lookup function values body callee returnShape lookup
  unfold lookupCodeHOLExact at exact
  split at exact
  · simp at exact
  · rename_i parameters program shape found
    split at exact
    · simp only [Option.some.injEq, Prod.mk.injEq] at exact
      obtain ⟨_, hcallee, _⟩ := exact
      rw [← hcallee]
      apply globals_foldl_absent
      intro mem
      obtain ⟨pair, hpair, hkey⟩ := List.mem_map.1 mem
      apply (ready function parameters program shape found).2
      rw [← hkey]
      exact (List.of_mem_zip hpair).1
    · simp at exact

#print axioms globals_callee_noTemp
theorem globals_noTemp_resVar {m : HolFiniteMapExact MlS (ValueHOL 64)} {name : MlS}
    (ne : name ≠ globalsTemp) (old : Option (ValueHOL 64)) (h : m.lookup globalsTemp = none) :
    (HolFiniteMapExact.resVarEq m (name, old)).lookup globalsTemp = none := by
  cases old with
  | none => simp [FDOMSUB_HOL, Ne.symm ne, h]
  | some v => simp [FUPDATE_HOL, Ne.symm ne, h]

theorem globals_noTemp_setVar {F : Type} {s : PanSemStateFiniteExact 64 F} {name : MlS}
    (ne : name ≠ globalsTemp) (value : ValueHOL 64) (h : s.locals.lookup globalsTemp = none) :
    (setVarHOLFinite name value s).locals.lookup globalsTemp = none := by
  simp [setVarHOLFinite, FUPDATE, ne, h]

theorem globals_valid_ne {F : Type} {s : PanSemStateFiniteExact 64 F} {name : MlS} {value : ValueHOL 64}
    (valid : isValidValueHOLFinite s .local name value = true) (h : s.locals.lookup globalsTemp = none) :
    name ≠ globalsTemp := by
  intro e; subst e
  simp [isValidValueHOLFinite, lookupKvarHOLFinite, h] at valid

#print axioms globals_noTemp_setVar
end InitECandidate.Runtime.FineCost
