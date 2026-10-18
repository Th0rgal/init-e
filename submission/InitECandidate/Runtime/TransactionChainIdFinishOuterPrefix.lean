import InitECandidate.Runtime.TransactionChainIdSource
import InitECandidate.Runtime.TransactionHeaderLowerFrame
import InitECandidate.Runtime.LocalAssignNormalValue
import InitECandidate.Runtime.NamedGlobalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The chain-ID header store followed by index initialization retains all
older input slices below the transaction and globals on normal completion. -/
theorem transaction_chain_id_finish_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (tx array count input inputLength word : BitVec 64)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (wordLocal : state.locals.lookup (ofString "w") = some (.val (.word word)))
    (valid : RlpSliceInputPrefix state array input inputLength count.toNat)
    (before : array.toNat + count.toNat * 16 ≤ tx.toNat)
    (fits : tx.toNat + 8 < 2^64)
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
      have frame := transaction_word_header_lower_frame state tx 8 word (ofString "w") txLocal wordLocal fits
      rw [stored] at frame
      have metadata := evaluateHOLFiniteState_metadata state
        (.store (.op .add [.var .local (ofString "tx"),.const 8]) (.var .local (ofString "w")))
      rw [stored] at metadata
      have retained : RlpSliceInputPrefix middle array input inputLength count.toNat :=
        rlp_slice_input_prefix_after_lower_frame state middle array count input inputLength tx valid before metadata.2.1 frame
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

#print axioms transaction_chain_id_finish_outer_prefix
end InitECandidate.Runtime
