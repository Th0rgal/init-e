import InitECandidate.Runtime.PtPGGD
import InitECandidate.Runtime.PtKoWsLGD
import InitECandidate.Runtime.RecFrameGDL
/-!
The final phase of the `process_transaction` segment (spine drops 90-97, around the creation-branch `get_account`):
the segment's fresh words `[Lo, Hg)` (`Hg` the heap pointer before the branch) join the outside words of the
registry (`OutX`). Every registry table's arrays lie below its heap pointer (each table is separated from another
one's canonical footprint, which contains all words at or above the heap pointer), and every header lies below it,
so `SI` at `Lo` with heap pointer `Hg` gives `PG` (registry with content at `Hg` against `OutX`); `PG` gives back
`PXR`. Word stores into `[Lo, Hg)` and changes at or above the registry bound or in the Keccak windows keep `PG`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString



section pg
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {D : BitVec 64 → Prop} {B : Bool}
  {Excl : BitVec 64 → Prop} {Lo Hg Hb Nj H0 : BitVec 64} {M0 : Mem}






/-- Changes at or above `Hb` or in the Keccak windows keep `PG`. -/
theorem pg_kpL {SP0 FM K Pd NB P0 : BitVec 64} {M M' : Mem} {G : GA}
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
    (h : PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M G) (keep : ∀ x, x.toNat < Hb.toNat → ¬ KPW K Pd x → M' x = M x) :
    PG n c T Out ko D B Excl Lo Hg Hb Nj M0 M' G := by
  obtain ⟨hh,reg,hn,fr⟩ := h
  refine ⟨hh,regT_keep_exceptL reg (KPW K Pd) keep ?_ ?_,hn,fun x ho hx => ?_⟩
  · intro x hc hk
    rcases hk with hk | hk
    · exact (safe x hc).2.1 hk
    · exact (safe x hc).2.2.1 hk
  · intro lo Hx hdr x hin hk
    rcases hk with hk | hk
    · exact (hkoWs lo Hx hdr x hin).2.1 hk
    · exact (hkoWs lo Hx hdr x hin).2.2.1 hk
  · have hnk : ¬ KPW K Pd x := by
      rintro (hk | hk)
      · exact (hOutSafe x ho).1.2.1 hk
      · exact (hOutSafe x ho).1.2.2.1 hk
    exact (keep x (regT_out_lt reg (Or.inl ho)) hnk).trans (fr x ho hx)


end pg
end InitECandidate.Runtime
