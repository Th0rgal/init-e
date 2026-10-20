import InitECandidate.Runtime.PtRestOGD
/-!
Audit: the premise form `∀ (Mx : Mem) (lo : TLay), lo.hdr Mx Tt → ∀ x, InTabF Tt lo.KS … x → WsSafe SP0 FM K Pd NB x`
(`hkoWs` in the process-transaction chain) is unsatisfiable: a memory whose header at `Tt` places the key array at the
keccak state `K` makes `K` a table word that is not `WsSafe`.
Affected (vacuous) modules, all theorems taking a `∀ (Mx : Mem) (lo : TLay), lo.hdr Mx (T ko) → …` premise (`hkoWs`,
`hkoSc`, the `hko` of `regT_keep_except(H)`) and their dependents (85 theorems):
  CheckTransactionGD, CheckTransactionUGD, ProcessTxFencedGD, ProcessTxPrefixGD, ProcessTxSGD, ProcessTxUGD
  ProcessTxWritersGD, PtAwClearGD, PtCcaPGGD, PtClearGD, PtCreateEtherGD, PtGaPGGD
  PtPGGD, PtRest2GD, PtRestAllGD, PtRestAllOGD, PtRestGD, PtRestOGD
  PtSegAllGD, PtSegBaseGD, PtSegFinGD, PtSegTxhGD, PtSufAGD, PtSufAO2GD
  PtSufAO3GD, PtSufAOGD, PtSufBGD, PtSufBO2GD, PtSufBOGD, PtSufCGD
  PtSufEGD, PtTxGD, PtTxO2GD, PtTxO3GD, PtTxOGD, RecFrameGD
Repair: `PtKoWsLGD` (`TabAvoid`, `KoWsL`, `wsSafe_of_low`, `tabAvoid_of_low`, `koWs_fixed`) and the `…L` variant modules
(premises replaced by the layout-validity form, satisfiable from the workspace floor and `L0 ≤ T ko`).
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem hkoWs_form_false (Tt SP0 FM K Pd NB : BitVec 64) (hK : K.toNat + 8 < 2 ^ 64) :
    ¬ ∀ (Mx : Mem) (lo : TLay), lo.hdr Mx Tt →
      ∀ x, InTabF Tt lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x → WsSafe SP0 FM K Pd NB x := by
  intro h
  let lo : TLay := ⟨0#64,8#64,1#64,0#64,K,0#64,0#64,0#64,0#64,0⟩
  let Mx : Mem := fun a => if a = Tt + 32#64 then .word K else if a = Tt + 8#64 then .word 8#64 else
    if a = Tt + 16#64 then .word 1#64 else .word 0#64
  have hd : lo.hdr Mx Tt := by
    simp only [TLay.hdr,Hdr,Mx,lo]
    simp
  have hin : InTabF Tt lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS K :=
    Or.inr (Or.inl ⟨le_refl _,by simp [lo] <;> omega⟩)
  exact (h Mx lo hd K hin).2.1 ⟨0,by decide,Or.inl (by simp)⟩

#print axioms hkoWs_form_false
end InitECandidate.Runtime
