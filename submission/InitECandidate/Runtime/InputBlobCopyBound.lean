import InitECandidate.Runtime.InputBlobLoopBound
import InitECandidate.Runtime.PanSeqStraightBound
import InitECandidate.Runtime.SszSplitVarListFirstStage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def inputBlobCopyBound (length : BitVec 64) : Nat := (length.toNat + 7) / 8

/-- Initializing the copy counters and returning the input pair adds no
ticks to the actual eight-byte shared-input loop bound. -/
theorem evaluate_inputBlob_copy_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (small : length.toNat ≤ 134217712) (budget : inputBlobCopyBound length ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (inputBlobAt 4)
    state.clock ≤ evaluated.2.clock + inputBlobCopyBound length ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let one := setVarHOLFinite (ofString "i") (.val (.word (0 : BitVec 64))) state
  let ready := setVarHOLFinite (ofString "w") (.val (.word (0 : BitVec 64))) one
  rw [source_inputBlob_stages.2.2.2.2.1]
  apply evaluate_dec_word_post state (ofString "i") (.const 0) _ (0 : BitVec 64) (inputBlobCopyBound length)
    (fun r _ => r ≠ some .timeOut) (fun _ _ _ h => h) (by simp [evalHOLExact])
  rw [source_inputBlob_stages.2.2.2.2.2.1]
  apply evaluate_dec_word_post one (ofString "w") (.const 0) _ (0 : BitVec 64) (inputBlobCopyBound length)
    (fun r _ => r ≠ some .timeOut) (fun _ _ _ h => h) (by simp [evalHOLExact])
  have i : ready.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))) := by
    simp [ready,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "w" ≠ ofString "i" by decide]
  have len : ready.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [ready,one,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atLength,
      show ofString "w" ≠ ofString "len" by decide,show ofString "i" ≠ ofString "len" by decide]
  obtain ⟨result,post,run,spent,kept,safe,_,_⟩ := evaluate_inputBlob_loop_bounded ready 0 length i len
    (by simp) small (by simpa [ready,one,setVarHOLFinite,inputBlobCopyBound] using budget)
  have loopBound : ready.clock ≤ (evaluateHOLFiniteState ready inputBlobLoop).2.clock + inputBlobCopyBound length ∧
      (evaluateHOLFiniteState ready inputBlobLoop).2.clock ≤ ready.clock ∧
      (evaluateHOLFiniteState ready inputBlobLoop).1 ≠ some .timeOut := by
    rw [run]
    simpa [inputBlobCopyBound] using And.intro spent (And.intro kept safe)
  rw [source_inputBlob_stages.2.2.2.2.2.2.1]
  exact evaluate_sequence_straight_bounded ready inputBlobLoop (inputBlobAt 7) (inputBlobCopyBound length)
    loopBound (by rw [source_inputBlob_stages.2.2.2.2.2.2.2]; rfl)

#print axioms evaluate_inputBlob_copy_bounded
end InitECandidate.Runtime
