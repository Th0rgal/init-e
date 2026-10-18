import InitECandidate.Runtime.HtrBytesVectorSource
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.MerkleMemoryBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def htrBytesVectorShortCost : Nat := 16 + merkleMemoryCallCost

theorem htrBytesVector_check_globals : OriginalGlobalsFrame htrBytesVectorCheck := by
  unfold htrBytesVectorCheck htrBytesVectorShort
  apply originalGlobalsFrame_conditional
  · exact originalGlobalsFrame_sequence _ _ (memzero_call_globals_frame _)
      (originalGlobalsFrame_sequence _ _ (memcpy_call_globals_frame _) (originalGlobalsFrame_leaf _ (by intro watched; rfl)))
  · exact originalGlobalsFrame_leaf _ (by intro watched; rfl)

theorem runBounded_htrBytesVector_short {F : Type} (state : PanSemStateFiniteExact 64 F)
    (p n out : BitVec 64)
    (hp : state.locals.lookup (ofString "p") = some (.val (.word p)))
    (hn : state.locals.lookup (ofString "n") = some (.val (.word n)))
    (ho : state.locals.lookup (ofString "out") = some (.val (.word out)))
    (small : n.toNat ≤ 134217712) (code : state.code = originalRuntimeCode)
    (budget : htrBytesVectorShortCost ≤ state.clock) :
    RunBounded state htrBytesVectorShort htrBytesVectorShortCost := by
  unfold htrBytesVectorShort
  refine RunBounded.seq (RunBounded.ofProg (memzero_const_progBounded _ 32 (by decide)) code (by unfold htrBytesVectorShortCost at budget; omega)) budget ?_
  intro next normal nextCode remaining
  have keep (key : MlS) : next.locals.lookup key = state.locals.lookup key := by
    have frame := evaluate_avoidsLocal_flowing key
      (.call (some (none,none)) (ofString "memzero") [.var .local (ofString "out"),.const 32]) rfl state
      (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using frame
  have args : evalListHOLFinite next (h := fun a => Classical.propDecidable (next.memaddrs a))
      [.var .local (ofString "out"),.var .local (ofString "p"),.var .local (ofString "n")] =
      some [.val (.word out),.val (.word p),.val (.word n)] := by
    simp [evalListHOLExact,evalHOLExact,keep,hp,hn,ho]
  have raw := evaluate_memcpy_call_bounded next _ out p n args (nextCode.trans code) (by omega)
    (by have cost := merkle_memory_call_cost_le n (by omega); omega)
  have bounded : RunBounded next (.call (some (none,none)) (ofString "memcpy")
      [.var .local (ofString "out"),.var .local (ofString "p"),.var .local (ofString "n")]) merkleMemoryCallCost :=
    RunBounded.weaken ⟨raw.1,raw.2.1,raw.2.2⟩ (merkle_memory_call_cost_le _ (by omega))
  have together := RunBounded.seq (tail := .return (.const 0)) (b := 0) bounded (by simpa using remaining) (by
    intro final done finalCode rest
    exact RunBounded.ofProg (ProgBounded.straight _ (by decide)) (finalCode.trans (nextCode.trans code)) rest)
  simpa using together

#print axioms htrBytesVector_check_globals
#print axioms runBounded_htrBytesVector_short
end InitECandidate.Runtime
