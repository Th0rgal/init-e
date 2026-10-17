import InitECandidate.Runtime.StoreAdvance8Loop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def keccakAbsorbChoice : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_keccak_absorb_block with
  | .dec _ _ _ (.seq choice _) => choice
  | _ => .skip

def keccakAbsorbAlignment : ExpHOL 64 :=
  match keccakAbsorbChoice with
  | .ite condition _ _ => condition
  | _ => .const 0

def keccakAbsorbAlignedStore : ExpHOL 64 × ExpHOL 64 :=
  match keccakAbsorbChoice with
  | .ite _ (.while _ (.seq (.store destination value) _)) _ => (destination,value)
  | _ => (.const 0,.const 0)

def keccakAbsorbUnalignedStore : ExpHOL 64 × ExpHOL 64 :=
  match keccakAbsorbChoice with
  | .ite _ _ (.while _ (.seq (.store destination value) _)) => (destination,value)
  | _ => (.const 0,.const 0)

theorem source_keccakAbsorb_loop_choice : keccakAbsorbChoice =
    .ite keccakAbsorbAlignment
      (.while storeAdvance8Condition (storeAdvance8Body keccakAbsorbAlignedStore.1 keccakAbsorbAlignedStore.2))
      (.while storeAdvance8Condition (storeAdvance8Body keccakAbsorbUnalignedStore.1 keccakAbsorbUnalignedStore.2)) := by
  simp only [keccakAbsorbAlignment,keccakAbsorbAlignedStore,keccakAbsorbUnalignedStore,keccakAbsorbChoice,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Both original absorption loops use at most seventeen source ticks,
including inaccessible or non-word memory causing an early error. -/
theorem evaluate_keccakAbsorb_loop_choice {F : Type} (state : PanSemStateFiniteExact 64 F)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (ticks : 17 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keccakAbsorbChoice = (result,post) ∧
      state.clock ≤ post.clock + 17 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ output, result ≠ some (.returned output)) := by
  have aligned := evaluate_store_advance8_loop state keccakAbsorbAlignedStore.1 keccakAbsorbAlignedStore.2 initial ticks
  have unaligned := evaluate_store_advance8_loop state keccakAbsorbUnalignedStore.1 keccakAbsorbUnalignedStore.2 initial ticks
  rw [source_keccakAbsorb_loop_choice,evaluateHOLFiniteState_ite]
  split
  · split
    · obtain ⟨result,post,run,cost,remaining,noTimeout,_,noReturn⟩ := unaligned
      exact ⟨result,post,run,cost,remaining,noTimeout,noReturn⟩
    · obtain ⟨result,post,run,cost,remaining,noTimeout,_,noReturn⟩ := aligned
      exact ⟨result,post,run,cost,remaining,noTimeout,noReturn⟩
  · exact ⟨_,_,rfl,by omega,Nat.le_refl _,by simp,by intro output; simp⟩

#print axioms source_keccakAbsorb_loop_choice
#print axioms evaluate_keccakAbsorb_loop_choice
end InitECandidate.Runtime
