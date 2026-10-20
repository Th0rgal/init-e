import InitECandidate.Runtime.KeccakWideMainLoopResult
import InitECandidate.Runtime.KeccakGeneralRemainderBound
import InitECandidate.Runtime.KeccakShortBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

theorem runBounded_keccak_wide_full_after_zero {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (atStp : state.locals.lookup (ofString "stp") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (small : size.toNat ≤ 2^62) (outAligned : output.toNat % 8 = 0)
    (code : state.code = originalRuntimeCode) (budget : size.toNat * 20 + 82 ≤ state.clock) :
    RunBounded state (stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_keccak256)) (size.toNat * 20 + 82) := by
  rw [source_keccak_after_state_zero]
  apply RunBounded.decConst
  let indexed := setVarHOLFinite (ofString "i") (.val (.word (0#64))) state
  have atI : indexed.locals.lookup (ofString "i") = some (.val (.word 0)) := by
    simp [indexed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have keep (key : MlS) (different : key ≠ ofString "i") : indexed.locals.lookup key = state.locals.lookup key := by
    simp [indexed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have n := (keep _ (by decide)).trans atN
  have p := (keep _ (by decide)).trans atP
  have stp := (keep _ (by decide)).trans atStp
  have first := runBounded_keccak_wide_main_loop indexed pointer source size code atI n p stp small (by change _ ≤ state.clock; omega)
  refine RunBounded.seq first budget ?_
  intro next normal nextCode remaining
  obtain ⟨⟨index,idx,inside,aligned,tailSmall⟩,globals,installed,domain,kept⟩ :=
    keccak_wide_main_loop_normal_result indexed next pointer source size code atI n p stp small (by change _ ≤ state.clock; omega) normal
  have atN' := (kept _ (by decide)).trans n
  have remainderNat : (size - index).toNat = size.toNat - index.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr inside)
  rw [source_keccak_remainder_scope]
  have evaluated : @evalHOLExact 64 F _ next.toExact (fun a => Classical.propDecidable (next.memaddrs a))
      (.op .sub [.var .local (ofString "n"),.var .local (ofString "i")]) = some (.val (.word (size - index))) := by
    simp [evalHOLExact,evalListHOLExact,atN',idx,wordOpHOL,wordOp,valueIsWord,valueWord]
  apply RunBounded.decWord next _ _ (size - index) evaluated
  let entered := setVarHOLFinite (ofString "rem") (.val (.word (size - index))) next
  have old (key : MlS) (different : key ≠ ofString "rem") : entered.locals.lookup key = next.locals.lookup key := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  exact runBounded_keccak_general_remainder entered pointer pad source index (size - index) output
    ((old _ (by decide)).trans ((kept _ (by decide)).trans stp))
    (by change next.globals.lookup _ = _; rw [globals]; exact atPad)
    ((old _ (by decide)).trans ((kept _ (by decide)).trans p)) ((old _ (by decide)).trans idx)
    (by simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    ((old _ (by decide)).trans ((kept _ (by decide)).trans ((keep _ (by decide)).trans atOut)))
    (by rw [remainderNat]; exact tailSmall) outAligned (nextCode.trans code) remaining

/-- The original Keccak body has a uniform input-linear bound through all
full blocks and the remainder. No input alignment/readability premise is needed. -/
theorem runBounded_keccak_wide_full_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output : BitVec 64)
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (small : size.toNat ≤ 2^62) (outAligned : output.toNat % 8 = 0)
    (code : state.code = originalRuntimeCode) (budget : size.toNat * 20 + 124 ≤ state.clock) :
    RunBounded state (sourceFunctionBody Guest.guestFn_keccak256) (size.toNat * 20 + 124) := by
  rw [source_keccak_body]
  have evaluated : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.var .global (ofString "keccak_st")) = some (.val (.word pointer)) := by simp [evalHOLExact,atState]
  apply RunBounded.decWord state _ _ pointer evaluated
  let entered := setVarHOLFinite (ofString "stp") (.val (.word pointer)) state
  have stp : entered.locals.lookup (ofString "stp") = some (.val (.word pointer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have keep (key : MlS) (different : key ≠ ofString "stp") : entered.locals.lookup key = state.locals.lookup key := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  let arguments : List (ExpHOL 64) := [.var .local (ofString "stp"),.const 200]
  have args : evalListHOLFinite entered (h := fun a => Classical.propDecidable (entered.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word (200#64))] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [arguments,evalListHOLExact,evalHOLExact,stp]
  have first : RunBounded entered (.call (some (none,none)) (ofString "memzero") arguments) 42 :=
    evaluate_memzero_call_bounded entered arguments pointer (200#64) args code (by decide) (by change 42 ≤ state.clock; omega)
  rw [source_keccak_state_zero_prefix]
  have whole : RunBounded entered (.seq (.call (some (none,none)) (ofString "memzero") arguments)
      (stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_keccak256))) (42 + (size.toNat * 20 + 82)) := by
    refine RunBounded.seq first (by change 42 + (size.toNat * 20 + 82) ≤ state.clock; omega) ?_
    intro next normal nextCode remaining
    have locals := evaluate_discard_call_success_locals entered (ofString "memzero") arguments (by rw [normal])
    have globals := memzero_call_globals_frame arguments entered code
    rw [normal] at locals globals
    exact runBounded_keccak_wide_full_after_zero next pointer pad source size output
      (by rw [locals]; exact stp) (by rw [globals]; exact atPad)
      (by rw [locals]; exact (keep _ (by decide)).trans atP)
      (by rw [locals]; exact (keep _ (by decide)).trans atN)
      (by rw [locals]; exact (keep _ (by decide)).trans atOut) small outAligned (nextCode.trans code) remaining
  exact whole.weaken (by omega)

#print axioms runBounded_keccak_wide_full_after_zero
#print axioms runBounded_keccak_wide_full_body
end InitECandidate.Runtime
