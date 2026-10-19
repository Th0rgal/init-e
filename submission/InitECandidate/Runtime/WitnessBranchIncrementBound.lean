import InitECandidate.Runtime.WitnessBranchFinishBound
import InitECandidate.Runtime.WitnessBranchSource
import InitECandidate.Runtime.WitnessExtensionStoresProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem runBounded_ite_branches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (condition : ExpHOL 64) (left right : ProgHOL 64) (cost : Nat)
    (first : RunBounded s left cost) (second : RunBounded s right cost) :
    RunBounded s (.ite condition left right) cost := by
  unfold RunBounded at first second ⊢
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact second
    · exact first
  · simp

theorem runBounded_witness_branch_increment {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64)=.word array)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
    (code : s.code=originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock) :
    RunBounded s (witnessBranchAt 4) (witnessBranchFinishCost length.toNat) := by
  have straight : ProgBounded (.assign .local (ofString "i")
      (.op .add [.var .local (ofString "i"),.const 1])) 0 := ProgBounded.straight _ rfl
  rw [source_witness_branch_increment]
  have whole := RunBounded.seq (tail := witnessBranchAt 5) (b := witnessBranchFinishCost length.toNat)
    (RunBounded.ofProg straight code (by omega)) (by simpa using budget) (by
      intro next normal nextCode ticks
      obtain ⟨value,evaluated,same⟩ := evaluate_local_assign_normal_value s next _ _ normal
      subst next
      let selected := setVarHOLFinite (ofString "i") value s
      have selectedTop : selected.locals.lookup (ofString "top")=some (.val (.word top)) := by
        simpa [selected,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "i" ≠ ofString "top" by decide] using atTop
      have parsed := runBounded_witness_branch_finish selected array pointer length scratch frame top ceiling inputLimit
        selectedTop arrayReadable arrayCell (slice.after_frame s selected array 16 pointer length rfl rfl rfl)
        inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena ticks
      have more : ProgBounded witnessBranchMore 0 := by
        apply ProgBounded.straight
        rw [source_witness_branch_more]
        rfl
      rw [source_witness_branch_dispatch]
      exact runBounded_ite_branches selected _ _ _ _
        ((RunBounded.ofProg (state := selected) more code (by omega)).weaken (by omega)) parsed)
  simpa using whole

#print axioms runBounded_ite_branches
#print axioms runBounded_witness_branch_increment
end InitECandidate.Runtime
