import InitECandidate.Runtime.MptInitFinishBound
import InitECandidate.Runtime.MptInitHashTailBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
theorem evaluate_mptInit_finish_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (hashGlobal : state.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word 2713717584)))
    (trieGlobal : state.globals.lookup (ofString "empty_trie_root") = some (.val (.word 2713717456)))
    (emptyGlobal : state.globals.lookup (ofString "empty_code_hash") = some (.val (.word 2713717488)))
    (code : state.code = originalRuntimeCode) (budget : 719 ≤ state.clock)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address) :
    let evaluated := evaluateHOLFiniteState state mptInitFinish
    state.clock ≤ evaluated.2.clock + 719 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have facts := evaluate_storeByte_control_frame state (.var .global (ofString "mpt_hash_scratch")) (.const 128)
  rw [mptInitFinish,evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state (.storeByte (.var .global (ofString "mpt_hash_scratch")) (.const 128)) with
  | mk result middle =>
    rw [run] at facts
    dsimp only at facts
    obtain ⟨control,clock,_,globals,installed,domain,_⟩ := facts
    rcases control with rfl | rfl
    · dsimp only
      have tail := evaluate_mptInit_hash_tail_bounded_cells middle
        (by rw [globals]; exact stateGlobal) (by rw [globals]; exact padGlobal)
        (by rw [globals]; exact hashGlobal) (by rw [globals]; exact trieGlobal)
        (by rw [globals]; exact emptyGlobal) (installed.trans code) (by omega)
        (by intro address aligned lower upper; rw [domain]; exact arena address aligned lower upper)
      exact ⟨by have cost := tail.1; omega,by have remaining := tail.2.1; omega,tail.2.2⟩
    · dsimp only
      exact ⟨by omega,by omega,by simp⟩

#print axioms evaluate_mptInit_finish_bounded_cells
end InitECandidate.Runtime
