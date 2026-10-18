import InitECandidate.Runtime.SszSplitVarListSource
import InitECandidate.Runtime.SszCheckOffsetsStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def wmem (m : BitVec 64 → HolWordLab 64) (address value : BitVec 64) : BitVec 64 → HolWordLab 64 :=
  fun current => if current = address then .word value else m current

theorem sszStore_in {σ : Type} (st : PanSemStateFiniteExact 64 σ) (address value : BitVec 64)
    (destination expression : ExpHOL 64)
    (hd : @evalHOLExact 64 σ _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) destination =
      some (.val (.word address)))
    (hv : @evalHOLExact 64 σ _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) expression =
      some (.val (.word value))) (dom : st.memaddrs address) :
    evaluateHOLFiniteState st (.store destination expression) =
      (none, {st with memory := wmem st.memory address value}) := by
  classical
  rw [evaluateHOLFiniteState_store, hd, hv]
  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, dom]
  rfl

theorem sszStore_out {σ : Type} (st : PanSemStateFiniteExact 64 σ) (address value : BitVec 64)
    (destination expression : ExpHOL 64)
    (hd : @evalHOLExact 64 σ _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) destination =
      some (.val (.word address)))
    (hv : @evalHOLExact 64 σ _ st.toExact (fun a => Classical.propDecidable (st.memaddrs a)) expression =
      some (.val (.word value))) (dom : ¬ st.memaddrs address) :
    evaluateHOLFiniteState st (.store destination expression) = (some .error, st) := by
  classical
  rw [evaluateHOLFiniteState_store, hd, hv]
  simp [flattenHOL, panMemStoresHOL, panMemStoreHOL, dom]

section
variable {σ : Type} (c : PanSemStateFiniteExact 64 σ)

theorem sszSplit_prevAddr (arr i : BitVec 64)
    (ha : c.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i))) :
    @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
      (.op .add [sszLocal "arr", .panop .mul [.op .sub [sszLocal "i", .const 1], .const 16], .const 8]) =
      some (.val (.word (arr + (i - 1) * 16 + 8))) := by
  simp [sszLocal, evalHOLExact, evalListHOLExact, ha, hi, wordOpHOL, wordOp, valueIsWord, valueWord, panOpHOL]
  exact (BitVec.add_assoc _ _ _).symm

theorem sszSplit_diff (x y : BitVec 64) (nx ny : String)
    (hx : c.locals.lookup (ofString nx) = some (.val (.word x)))
    (hy : c.locals.lookup (ofString ny) = some (.val (.word y))) :
    @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
      (.op .sub [sszLocal nx, sszLocal ny]) = some (.val (.word (x - y))) := by
  simp [sszLocal, evalHOLExact, evalListHOLExact, hx, hy, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem sszSplit_sum (x y : BitVec 64) (nx ny : String)
    (hx : c.locals.lookup (ofString nx) = some (.val (.word x)))
    (hy : c.locals.lookup (ofString ny) = some (.val (.word y))) :
    @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
      (.op .add [sszLocal nx, sszLocal ny]) = some (.val (.word (x + y))) := by
  simp [sszLocal, evalHOLExact, evalListHOLExact, hx, hy, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem sszSplit_curAddr (arr i : BitVec 64)
    (ha : c.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (hi : c.locals.lookup (ofString "i") = some (.val (.word i))) :
    @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
      (.op .add [sszLocal "arr", .panop .mul [sszLocal "i", .const 16]]) =
      some (.val (.word (arr + i * 16))) := by
  simp [sszLocal, evalHOLExact, evalListHOLExact, ha, hi, wordOpHOL, wordOp, valueIsWord, valueWord, panOpHOL]

theorem sszSplit_tailAddr (arr count : BitVec 64)
    (ha : c.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (hc : c.locals.lookup (ofString "count") = some (.val (.word count))) :
    @evalHOLExact 64 σ _ c.toExact (fun a => Classical.propDecidable (c.memaddrs a))
      (.op .add [sszLocal "arr", .panop .mul [.op .sub [sszLocal "count", .const 1], .const 16], .const 8]) =
      some (.val (.word (arr + (count - 1) * 16 + 8))) := by
  simp [sszLocal, evalHOLExact, evalListHOLExact, ha, hc, wordOpHOL, wordOp, valueIsWord, valueWord, panOpHOL]
  exact (BitVec.add_assoc _ _ _).symm

theorem sszSplitCheck_pass (o first len prev : BitVec 64)
    (ho : c.locals.lookup (ofString "o") = some (.val (.word o)))
    (hf : c.locals.lookup (ofString "first") = some (.val (.word first)))
    (hl : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (hp : c.locals.lookup (ofString "prev") = some (.val (.word prev)))
    (ok : ¬ o < first ∧ ¬ len < o ∧ ¬ o < prev) :
    evaluateHOLFiniteState c sszSplitCheck = (none, c) := by
  unfold sszSplitCheck
  simp [sszLocal, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, ho, hf, hl, hp, ok.1, ok.2.1, ok.2.2,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, orop_eq]

theorem sszSplitCheck_fail (o first len prev : BitVec 64)
    (ho : c.locals.lookup (ofString "o") = some (.val (.word o)))
    (hf : c.locals.lookup (ofString "first") = some (.val (.word first)))
    (hl : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (hp : c.locals.lookup (ofString "prev") = some (.val (.word prev)))
    (bad : o < first ∨ len < o ∨ o < prev) :
    evaluateHOLFiniteState c sszSplitCheck =
      evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const 23]) := by
  unfold sszSplitCheck
  have value : (if o < first then 1#64 else 0#64) ||| ((if len < o then 1#64 else 0#64) |||
      (if o < prev then 1#64 else 0#64)) ≠ 0#64 := by
    rcases bad with bad | bad | bad <;> simp [bad] <;> split <;> split <;> decide
  simp [sszLocal, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, ho, hf, hl, hp,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, orop_eq,
    Ne.symm value, -evaluateHOLFiniteState_call]

end

#print axioms sszSplitCheck_fail
end InitECandidate.Runtime
