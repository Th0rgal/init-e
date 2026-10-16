import InitECandidate.Runtime.MemzeroSyntax
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem eval_memzeroBase {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) memzeroBase =
        some (.val (.word (destination + index))) := by
  simp [memzeroBase,evalHOLExact,evalListHOLExact,dstLocal,indexLocal,wordOpHOL,wordOp,valueIsWord,valueWord]

theorem eval_memzeroOffset {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index offset : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) (memzeroOffset offset) =
        some (.val (.word (destination + index + offset))) := by
  simp [memzeroOffset,evalHOLExact,evalListHOLExact,dstLocal,indexLocal,wordOpHOL,wordOp,
    valueIsWord,valueWord,BitVec.add_assoc]

theorem evaluate_memzero_word8_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain : state.memaddrs (destination + index)) :
    evaluateHOLFiniteState state memzeroWord8Body =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 8)))
        (sourceWriteWord state (destination + index) 0)) := by
  have store := evaluate_store_word state (destination + index) 0 memzeroBase (.const 0)
    (eval_memzeroBase state destination index dstLocal indexLocal) (by rfl) domain
  exact evaluate_seq_none store (evaluate_memzero_advance _ index 8 indexLocal)

/-- The four actual source stores of the 32-byte aligned block preserve all
locals until the final i += 32 assignment. -/
theorem evaluate_memzero_word32_body {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination index : BitVec 64)
    (dstLocal : state.locals.lookup (ofString "dst") = some (.val (.word destination)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (domain0 : state.memaddrs (destination + index))
    (domain8 : state.memaddrs (destination + index + 8))
    (domain16 : state.memaddrs (destination + index + 16))
    (domain24 : state.memaddrs (destination + index + 24)) :
    evaluateHOLFiniteState state memzeroWord32Body =
      (none,setVarHOLFinite (ofString "i") (.val (.word (index + 32)))
        (sourceWriteWord (sourceWriteWord (sourceWriteWord (sourceWriteWord state
          (destination + index) 0) (destination + index + 8) 0)
          (destination + index + 16) 0) (destination + index + 24) 0)) := by
  let one := sourceWriteWord state (destination + index) 0
  let two := sourceWriteWord one (destination + index + 8) 0
  let three := sourceWriteWord two (destination + index + 16) 0
  let four := sourceWriteWord three (destination + index + 24) 0
  have store0 := evaluate_store_word state (destination + index) 0 memzeroBase (.const 0)
    (eval_memzeroBase state destination index dstLocal indexLocal) (by rfl) domain0
  have store8 := evaluate_store_word one (destination + index + 8) 0 (memzeroOffset 8) (.const 0)
    (eval_memzeroOffset one destination index 8 dstLocal indexLocal) (by rfl) domain8
  have store16 := evaluate_store_word two (destination + index + 16) 0 (memzeroOffset 16) (.const 0)
    (eval_memzeroOffset two destination index 16 dstLocal indexLocal) (by rfl) domain16
  have store24 := evaluate_store_word three (destination + index + 24) 0 (memzeroOffset 24) (.const 0)
    (eval_memzeroOffset three destination index 24 dstLocal indexLocal) (by rfl) domain24
  have advance := evaluate_memzero_advance four index 32 indexLocal
  exact evaluate_seq_none store0 (evaluate_seq_none store8 (evaluate_seq_none store16 (evaluate_seq_none store24 advance)))

/-- Bounds from a valid allocation prevent the source block counter wrapping.
Every taken block guard decreases remaining bytes by its positive stride. -/
theorem memzero_counter_progress (index size stride : BitVec 64)
    (inside : index.toNat ≤ size.toNat) (small : size.toNat ≤ 33806089496)
    (strideBound : stride.toNat ≤ 32) (positive : 0 < stride.toNat)
    (guard : index + stride ≤ size) :
    (index + stride).toNat = index.toNat + stride.toNat ∧
      (index + stride).toNat ≤ size.toNat ∧
      size.toNat - (index + stride).toNat < size.toNat - index.toNat := by
  have noWrap : index.toNat + stride.toNat < 2 ^ 64 := by omega
  have advanced := BitVec.toNat_add_of_lt noWrap
  have bounded := BitVec.le_def.mp guard
  rw [advanced] at bounded
  exact ⟨advanced,by omega,by omega⟩

#print axioms evaluate_memzero_word8_body
#print axioms evaluate_memzero_word32_body
#print axioms memzero_counter_progress
end InitECandidate.Runtime
