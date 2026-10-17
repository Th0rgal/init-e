import InitECandidate.Runtime.StateStorageInnerSelection
import InitECandidate.Runtime.TransactionStorageValueAllRequests
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The existing-table branch assigns m.1 to inner and executes the original
value tail. Registration of that selected pointer is an explicit lookup invariant. -/
theorem TransactionRegistryWorld.storage_existing_inner {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer inner key a b c d present oldInner : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : inner ∈ tables)
    (innerLocal : state.locals.lookup (ofString "inner") = some (.val (.word oldInner)))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word present),.val (.word inner)]))
    (nonzero : present ≠ 0)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 73 + 2 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageInnerSelection = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 73 + 2) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) post) := by
  let selected := setVarHOLFinite (ofString "inner") (.val (.word inner)) state
  have condition : @evalHOLExact 64 F _ state.toExact (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0)) = some (.val (.word (0 : BitVec 64))) := by
    simp [evalHOLExact,mLocal,Compiler.Encoders.Asm.wordCmpHOL]
    exact nonzero
  have assignment : evaluateHOLFiniteState state (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m")))) = (none,selected) := by
    simp [evaluateHOLFiniteState_assign,evalHOLExact,mLocal,isValidValueHOLExact,lookupKvarHOLExact,innerLocal,
      shapeOfHOLExact,shapeEqHOL,setKvarHOLFinite,selected]
  have selection : evaluateHOLFiniteState state
      (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0))
        (.seq (.call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32,.const 8])
          (.call (some (none,none)) (ofString "jset") [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")]))
        (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m"))))) = (none,selected) := by
    rw [evaluateHOLFiniteState_ite,condition]
    simpa using assignment
  have selectedValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count selected := valid.after_read rfl rfl rfl rfl rfl
  have atInner : selected.locals.lookup (ofString "inner") = some (.val (.word inner)) := by
    simp [selected,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atKey : selected.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simpa [selected,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "inner" ≠ ofString "key" from by decide] using keyLocal
  have atValue : selected.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]) := by
    simpa [selected,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "inner" ≠ ofString "value" from by decide] using valueLocal
  obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := selectedValid.storage_value_tail_all_requests selected widths tables fieldPointer ts journal snapshot count pointer inner key a b c d
    member atInner atKey atValue heap keyAligned keyWords keyBytes ticks
  exact ⟨result,post,evaluate_seq_none selection run,cost,remaining,noTimeout,preserved⟩

#print axioms TransactionRegistryWorld.storage_existing_inner
end InitECandidate.Runtime
