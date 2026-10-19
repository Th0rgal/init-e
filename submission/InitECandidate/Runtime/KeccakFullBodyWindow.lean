import InitECandidate.Runtime.KeccakFullSuffixWindow
import InitECandidate.Runtime.KeccakFullBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-- Full-length hashing writes only the permutation state, pad and output
windows. The frame covers failures as well as normal returns. -/
theorem keccak_full_body_window {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer pad source size output watched : BitVec 64)
    (atState : state.globals.lookup (ofString "keccak_st") = some (.val (.word pointer)))
    (atPad : state.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atP : state.locals.lookup (ofString "p") = some (.val (.word source)))
    (atN : state.locals.lookup (ofString "n") = some (.val (.word size)))
    (atOut : state.locals.lookup (ofString "out") = some (.val (.word output)))
    (small : size.toNat ≤ 134217712)
    (code : state.code = originalRuntimeCode) (budget : size.toNat * 20 + 42 ≤ state.clock)
    (outsideState : ¬ MWin pointer 200 watched) (outsidePad : ¬ MWin pad 136 watched)
    (outsideOutput : ¬ MWin output 32 watched) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak256)).2.memory watched = state.memory watched := by
  rw [source_keccak_body]
  apply dec_watch
  intro v hv
  have value : v = .val (.word pointer) := by simpa [evalHOLExact,atState] using hv.symm
  subst value
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
  have bounded := evaluate_memzero_call_bounded entered arguments pointer (200#64) args code (by decide)
    (by change 42 ≤ state.clock; omega)
  have frame := memzeroCall_watch entered.locals entered.globals arguments pointer 200 watched
    (fun t r => by rw [evalListHOLFinite_eq_toExact]; simp [arguments,evalListHOLExact,evalHOLExact,r.2.1,stp])
    (by decide) outsideState entered ⟨code,rfl,rfl⟩
  rw [source_keccak_state_zero_prefix,evaluateHOLFiniteState_seq_line780]
  cases zeroRun : evaluateHOLFiniteState entered (.call (some (none,none)) (ofString "memzero") arguments) with
  | mk result next =>
    rw [zeroRun] at frame
    cases result with
    | some r => exact frame.1
    | none =>
      have locals := evaluate_discard_call_success_locals entered (ofString "memzero") arguments (by rw [zeroRun])
      rw [zeroRun] at locals
      have globals := memzero_call_globals_frame arguments entered code
      rw [zeroRun] at globals
      have metadata := evaluateHOLFiniteState_metadata entered (.call (some (none,none)) (ofString "memzero") arguments)
      rw [zeroRun] at metadata
      have cost := bounded.1
      rw [zeroRun] at cost
      have tailFrame := keccak_full_after_zero_window next pointer pad source size output watched
        (by rw [locals]; exact stp) (by rw [globals]; exact atPad)
        (by rw [locals]; exact (keep _ (by decide)).trans atP)
        (by rw [locals]; exact (keep _ (by decide)).trans atN)
        (by rw [locals]; exact (keep _ (by decide)).trans atOut)
        small (metadata.1.trans code) (by change state.clock ≤ next.clock + 42 at cost; omega)
        outsideState outsidePad outsideOutput
      exact tailFrame.trans frame.1

#print axioms keccak_full_body_window
end InitECandidate.Runtime
