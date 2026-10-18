import InitECandidate.Runtime.MptInitHashTailBound
import InitECandidate.Runtime.KeccakInitializerCallBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
theorem evaluate_mptInit_hash_tail_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (hashGlobal : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word 2713717584)))
    (trieGlobal : state.globals.lookup (ofString "empty_trie_root") = some (.val (.word 2713717456)))
    (emptyGlobal : state.globals.lookup (ofString "empty_code_hash") = some (.val (.word 2713717488)))
    (code : state.code = originalRuntimeCode) (budget : 719 ≤ state.clock)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    let evaluated := evaluateHOLFiniteState state mptInitHashTail
    state.clock ≤ evaluated.2.clock + 719 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have firstArgs : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      mptInitFirstArguments = some [.val (.word 2713717584),.val (.word 1),.val (.word 2713717456)] := by
    simp [mptInitFirstArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,hashGlobal,trieGlobal]
  have first := evaluate_keccak_initializer_call_bounded_cells state _ _ _ 2713717584 1 2713717456
    stateGlobal padGlobal code (by change 360 ≤ state.clock; omega) firstArgs
    (by decide) (by decide) (by decide) (by decide) (by decide) arena
  let firstCall : ProgHOL 64 := .call (some (none,none)) (ofString "keccak256") mptInitFirstArguments
  change state.clock ≤ (evaluateHOLFiniteState state firstCall).2.clock + 360 ∧
    (evaluateHOLFiniteState state firstCall).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state firstCall).1 ≠ some .timeOut ∧
    (evaluateHOLFiniteState state firstCall).2.globals = state.globals ∧
    (evaluateHOLFiniteState state firstCall).2.code = state.code ∧
    (evaluateHOLFiniteState state firstCall).2.memaddrs = state.memaddrs at first
  rw [mptInitHashTail,evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "keccak256") mptInitFirstArguments) with
  | mk result middle =>
    rw [run] at first
    dsimp only at first
    obtain ⟨cost,remaining,noTimeout,globals,installed,domain⟩ := first
    cases result with
    | some _ =>
      dsimp only
      exact ⟨by omega,remaining,noTimeout⟩
    | none =>
      dsimp only
      have args : evalListHOLFinite middle (h := fun a => Classical.propDecidable (middle.memaddrs a))
          mptInitSecondArguments = some [.val (.word 2713717584),.val (.word 0),.val (.word 2713717488)] := by
        simp [mptInitSecondArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,globals,hashGlobal,emptyGlobal]
      have second := evaluate_keccak_initializer_call_bounded_cells middle _ _ _ 2713717584 0 2713717488
        (by rw [globals]; exact stateGlobal) (by rw [globals]; exact padGlobal) (installed.trans code)
        (by change 359 ≤ middle.clock; omega) args
        (by decide) (by decide) (by decide) (by decide) (by decide)
        (by intro address aligned lower upper; rw [domain]; exact arena address aligned lower upper)
      have secondCost : middle.clock ≤ (evaluateHOLFiniteState middle
          (.call (some (none,none)) (ofString "keccak256") mptInitSecondArguments)).2.clock + 359 := by
        have consumed := second.1
        change middle.clock ≤ (evaluateHOLFiniteState middle
          (.call (some (none,none)) (ofString "keccak256") mptInitSecondArguments)).2.clock + 0 + 359 at consumed
        simpa only [Nat.add_zero] using consumed
      have tail := evaluate_sequence_code_bounded middle
        (.call (some (none,none)) (ofString "keccak256") mptInitSecondArguments) (.return (.const 0)) 359 0
        ⟨secondCost,second.2.1,second.2.2.1⟩
        (by intro next _ _; simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,emptyLocalsHOLFinite])
        (by omega)
      exact ⟨by have consumed := tail.1; omega,by have kept := tail.2.1; omega,tail.2.2⟩

#print axioms evaluate_mptInit_hash_tail_bounded_cells
end InitECandidate.Runtime
