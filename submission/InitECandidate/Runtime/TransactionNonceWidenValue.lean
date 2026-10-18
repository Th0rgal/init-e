import InitECandidate.Runtime.TransactionNonceSource
import InitECandidate.Runtime.LocalAssignNormalValue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The type-4 nonce conversion installs the scalar word followed by three
zero limbs. A successful conversion changes only its destination local. -/
theorem transaction_nonce_widen_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (word : BitVec 64)
    (binding : state.locals.lookup (ofString "w") = some (.val (.word word)))
    (run : evaluateHOLFiniteState state transactionNonceWiden = (none,post)) :
    post = setVarHOLFinite (ofString "v")
      (.rStruct [.val (.word word),.val (.word 0),.val (.word 0),.val (.word 0)]) state := by
  obtain ⟨value,evaluated,updated⟩ := evaluate_local_assign_normal_value state post
    (ofString "v") _ run
  have expression : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.rstruct [.var .local (ofString "w"),.const 0,.const 0,.const 0]) =
      some (.rStruct [.val (.word word),.val (.word 0),.val (.word 0),.val (.word 0)]) := by
    simp [evalHOLExact,evalListHOLExact,binding]
  rw [expression] at evaluated
  cases evaluated
  exact updated

theorem transaction_nonce_widen_value_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (word : BitVec 64)
    (binding : state.locals.lookup (ofString "w") = some (.val (.word word)))
    (run : evaluateHOLFiniteState state transactionNonceWiden = (none,post)) :
    post.locals.lookup (ofString "v") =
      some (.rStruct [.val (.word word),.val (.word 0),.val (.word 0),.val (.word 0)]) ∧
    post.memory = state.memory ∧ post.globals = state.globals ∧
    post.clock = state.clock := by
  rw [transaction_nonce_widen_normal state post word binding run]
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms transaction_nonce_widen_normal
#print axioms transaction_nonce_widen_value_frame
end InitECandidate.Runtime
