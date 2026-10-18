import InitECandidate.Runtime.TransactionChainIdSource
import InitECandidate.Runtime.TransactionWordHeaderPrefix
import InitECandidate.Runtime.LocalAssignNormalValue
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The chain-ID header store followed by index initialization retains all
input slices and globals on normal completion. -/
theorem transaction_chain_id_finish_normal_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx array count input inputLength word : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word word)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : tx.toNat + 8 < array.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (run : evaluateHOLFiniteState state transactionChainIdFinish = (none,post)) :
    (∀ watched, post.globals.lookup watched = state.globals.lookup watched) ∧
    RlpSliceInputPrefix post array input inputLength count.toNat ∧
    post.locals.lookup (ofString "k") = some (.val (.word (1 : BitVec 64))) := by
  have globals : ∀ watched, post.globals.lookup watched = state.globals.lookup watched := by
    intro watched
    have kept := evaluate_avoidsGlobalAssignment watched transactionChainIdFinish (by rfl) state
    rw [run] at kept
    exact kept
  unfold transactionChainIdFinish at run
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases stored : evaluateHOLFiniteState state
      (.store (.op .add [.var .local (ofString "tx"),.const 8]) (.var .local (ofString "w"))) with
  | mk result middle =>
    rw [stored] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      have retained := transaction_word_header_prefix state tx 8 array count input inputLength word (ofString "w")
        txLocal wordLocal valid (by change tx.toNat + 8 < array.toNat; exact before) fits
      rw [stored] at retained
      obtain ⟨value,evaluated,updated⟩ := evaluate_local_assign_normal_value middle post (ofString "k") (.const 1) run
      have parsed : value = .val (.word (1 : BitVec 64)) := by
        simpa [evalHOLExact] using evaluated.symm
      rw [parsed] at updated
      refine ⟨globals,?_,?_⟩
      · rw [updated]
        intro slot bounded
        obtain ⟨p,n,item⟩ := retained slot bounded
        exact ⟨p,n,item.after_frame middle _ array slot p n input inputLength rfl rfl rfl⟩
      · rw [updated]
        simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms transaction_chain_id_finish_normal_frame
end InitECandidate.Runtime
