import InitECandidate.Runtime.TransactionLegacyPathTopContract
import InitECandidate.Runtime.TransactionTypeBranchBelow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_branch_normal_top_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionTypeParseBranch = (none,post)) :
    ∃ tag payloadPointer payload total : BitVec 64,
      post.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word payloadPointer),.val (.word payload),.val (.word total)]) ∧
      (tag = 0 ∨ tag = 1) ∧ payload.toNat ≤ length.toNat ∧ total.toNat ≤ length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧ post.globals = state.globals := by
  have range := transaction_typed_decode_range pointer length positive inputRange
  have factor : (2 * (length - 1).toNat + 1) * 15 + 19 ≤ (2 * length.toNat + 1) * 15 + 19 := by omega
  have product := Nat.mul_le_mul range.2.2.2 factor
  have typedBudget : (length - 1).toNat * ((2 * (length - 1).toNat + 1) * 15 + 19) + 92634 ≤ state.clock := by omega
  rw [source_transaction_type_branch,evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · rw [evaluateHOLFiniteState_ite] at run
      split at run
      · split at run
        · have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 2)
          rw [run] at terminal
          exact False.elim (terminal rfl)
        · obtain ⟨tag,payloadPointer,payload,atTop,tagBound,payloadBound,ends,noWrap,starts,globals⟩ :=
            transaction_legacy_path_normal_top_contract state post pointer length scratch frame ceiling inputLimit
              pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run
          exact ⟨tag,payloadPointer,payload,length,atTop,tagBound,payloadBound,Nat.le_refl _,ends,noWrap,starts,globals⟩
      · cases run
    · obtain ⟨tag,payloadPointer,payload,atTop,tagBound,payloadBound,ends,noWrap,starts,globals⟩ :=
        transaction_typed_path_normal_top_contract state post pointer length scratch frame ceiling inputLimit
          pointerLocal lengthLocal positive inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena typedBudget run
      exact ⟨tag,payloadPointer,payload,length - 1,atTop,tagBound,payloadBound,range.2.2.2,ends,noWrap,starts,globals⟩
  · cases run

#print axioms transaction_type_branch_normal_top_contract
end InitECandidate.Runtime
