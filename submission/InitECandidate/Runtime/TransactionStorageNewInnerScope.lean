import InitECandidate.Runtime.TransactionStorageNewInner
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original inner=0 scope also retains the enlarged registry after the
new-table path returns and restores the caller's inner binding. -/
theorem TransactionRegistryWorld.storage_new_inner_scope {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer outer addr key a b c d lookupValue : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (outerMember : outer ∈ tables)
    (outerLocal : state.locals.lookup (ofString "outer") = some (.val (.word outer)))
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (space : pointer.toNat + 762 ≤ 33806089496)
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 74 + 19 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageInnerScope = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 74 + 19) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld (withTableWidth widths pointer 32)
        (insert pointer tables) fieldPointer ts journal snapshot ((count + 1) + 1) post) := by
  let entered := setVarHOLFinite (ofString "inner") (.val (.word (0 : BitVec 64))) state
  have enteredValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count entered := valid.after_read rfl rfl rfl rfl rfl
  have atInner : entered.locals.lookup (ofString "inner") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have locals : ∀ name, name ≠ ofString "inner" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := enteredValid.storage_new_inner entered widths tables
    fieldPointer ts journal snapshot count pointer outer addr key a b c d 0 lookupValue outerMember atInner
    ((locals (ofString "outer") (by decide)).trans outerLocal) ((locals (ofString "addr") (by decide)).trans addrLocal)
    ((locals (ofString "key") (by decide)).trans keyLocal) ((locals (ofString "value") (by decide)).trans valueLocal)
    ((locals (ofString "m") (by decide)).trans mLocal) heap space addrAligned keyAligned addrWords addrBytes keyWords keyBytes ticks
  have full : evaluateHOLFiniteState state stateStorageInnerScope =
      (let output := evaluateHOLFiniteState entered stateStorageInnerSelection;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "inner",state.locals.lookup (ofString "inner"))})) := by
    unfold stateStorageInnerScope
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    rfl
  rw [run] at full
  dsimp only at full
  refine ⟨result,_,full,cost,remaining,noTimeout,?_⟩
  intro value success
  exact (preserved value success).after_read rfl rfl rfl rfl rfl

#print axioms TransactionRegistryWorld.storage_new_inner_scope
end InitECandidate.Runtime
