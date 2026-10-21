import InitECandidate.Runtime.U256LtTrace
import InitECandidate.Runtime.GuestCostOpAdd
import InitECandidate.Runtime.GuestCostOpAddLookup
import InitECandidate.Runtime.VmFn_u256_lt
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Two local-variable arguments with arbitrary names. -/
theorem evalListHOLFinite_two_named (s : PanSemStateFiniteExact 64 F)
    (x y : MlStringHOL) (vx vy : ValueHOL 64)
    (hx : s.locals.lookup x = some vx)
    (hy : s.locals.lookup y = some vy) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var VarKind.local x, .var VarKind.local y] = some [vx, vy] := by
  simp [evalListHOLFinite, evalListHOLExact, evalHOLExact, hx, hy]

/-- Installed `u256_lt` lookup with two four-word arguments. -/
theorem u256Lt_lookup (code : MlS → Option (List (MlS × ShapeHOL) ×
    ProgHOL 64 × ShapeHOL)) (installed : code = originalRuntimeCode.lookup)
    (vx vy : ValueHOL 64)
    (hx : shapeEqHOL comb4Shape (shapeOfHOLExact vx) = true)
    (hy : shapeEqHOL comb4Shape (shapeOfHOLExact vy) = true) :
    lookupCodeHOLFinite code (ofString "u256_lt") [vx, vy] =
      some (sourceFunctionBody Guest.guestFn_u256_lt,
        (HolFiniteMapExact.empty.update (ofString "a", vx)).update (ofString "b", vy),
        .one) := by
  have entry : code (ofString "u256_lt") =
      some ([(ofString "a", .comb [.one, .one, .one, .one]),
        (ofString "b", .comb [.one, .one, .one, .one])],
        sourceFunctionBody Guest.guestFn_u256_lt, .one) := by
    rw [installed]
    exact vmLookup_u256_lt
  have different : (ofString "a" : MlS) ≠ ofString "b" := by decide_cbv
  have := pan_two_shape_lookup code (ofString "u256_lt") (ofString "a") (ofString "b")
    (sourceFunctionBody Guest.guestFn_u256_lt) (.comb [.one, .one, .one, .one])
    (.comb [.one, .one, .one, .one]) .one vx vy
    different entry (by simpa [comb4Shape] using hx) (by simpa [comb4Shape] using hy)
  simpa [comb4Shape] using this

/-- Four-word value used by the comparison wrappers. -/
def fourValue (a0 a1 a2 a3 : BitVec 64) : ValueHOL 64 :=
  .rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]

/-- Callee bindings for the swapped `u256_lt` call: `a` is the second operand,
`b` the first. -/
def u256LtCallee (va vb : ValueHOL 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "a", vb)).update (ofString "b", va)

/-- Actual `u256_gt` wrapper: calls `u256_lt` with the two arguments swapped. -/
theorem u256Gt_run (s : PanSemStateFiniteExact 64 F)
    (a0 a1 a2 a3 b0 b1 b2 b3 : BitVec 64)
    (installed : s.code.lookup = originalRuntimeCode.lookup)
    (clock : s.clock ≠ 0) (clockTwo : 2 ≤ s.clock)
    (hA : s.locals.lookup (ofString "a") =
      some (.rStruct [.val (.word a0), .val (.word a1), .val (.word a2), .val (.word a3)]))
    (hB : s.locals.lookup (ofString "b") =
      some (.rStruct [.val (.word b0), .val (.word b1), .val (.word b2), .val (.word b3)])) :
    ∃ events, StatementRun s (sourceFunctionBody Guest.guestFn_u256_gt)
      (some (.returned (.val (.word (u256LtValue b0 b1 b2 b3 a0 a1 a2 a3)))))
      (emptyLocalsHOLFinite
        (emptyLocalsHOLFinite (callEntryStateHOLFinite s
          (u256LtCallee (fourValue a0 a1 a2 a3) (fourValue b0 b1 b2 b3))))) events := by
  classical
  let vb : ValueHOL 64 := fourValue b0 b1 b2 b3
  let va : ValueHOL 64 := fourValue a0 a1 a2 a3
  let callee := u256LtCallee va vb
  have hvB : shapeEqHOL comb4Shape (shapeOfHOLExact vb) = true := by
    simp [vb, fourValue, comb4Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  have hvA : shapeEqHOL comb4Shape (shapeOfHOLExact va) = true := by
    simp [va, fourValue, comb4Shape, shapeOfHOLExact, shapeEqHOL, shapeEqHOL.shapeEqListHOL]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.var VarKind.local (ofString "b"), .var VarKind.local (ofString "a")] =
      some [vb, va] := by
    simpa [vb, va] using evalListHOLFinite_two_named s (ofString "b") (ofString "a") vb va hB hA
  have lookup := u256Lt_lookup s.code.lookup installed vb va hvB hvA
  have bodyA : (callEntryStateHOLFinite s callee).locals.lookup (ofString "a") = some vb := by
    simp [callEntryStateHOLFinite, callee, u256LtCallee,
      HolFiniteMapExact.lookup_update_pointwise, FUPDATE,
      show (ofString "a" : MlS) ≠ ofString "b" by decide_cbv,
      show (ofString "b" : MlS) ≠ ofString "a" by decide_cbv]
  have bodyB : (callEntryStateHOLFinite s callee).locals.lookup (ofString "b") = some va := by
    simp [callEntryStateHOLFinite, callee, u256LtCallee,
      HolFiniteMapExact.lookup_update_pointwise, FUPDATE,
      show (ofString "b" : MlS) ≠ ofString "a" by decide_cbv]
  have bodyClock : (callEntryStateHOLFinite s callee).clock ≠ 0 := by
    simp [callEntryStateHOLFinite]
    omega
  obtain ⟨bodyEvents, bodyRun⟩ := u256Lt_run (callEntryStateHOLFinite s callee)
    b0 b1 b2 b3 a0 a1 a2 a3 bodyA bodyB
  have plan : callCostPlan s none .one
      (some (.returned (.val (.word (u256LtValue b0 b1 b2 b3 a0 a1 a2 a3)))))
      (emptyLocalsHOLFinite (callEntryStateHOLFinite s callee)) =
      .done (some (.returned (.val (.word (u256LtValue b0 b1 b2 b3 a0 a1 a2 a3)))))
        (emptyLocalsHOLFinite (emptyLocalsHOLFinite (callEntryStateHOLFinite s callee))) := by
    simp [callCostPlan, shapeEqHOL, shapeOfHOLExact, shapeEqHOL.shapeEqListHOL]
  have callRun := (call_statement_work (coeff := {}) args lookup clock bodyRun plan).1
  rw [source_u256Gt_body]
  exact ⟨_, callRun⟩

#print axioms u256Gt_run
end InitECandidate.Runtime.FineCost
