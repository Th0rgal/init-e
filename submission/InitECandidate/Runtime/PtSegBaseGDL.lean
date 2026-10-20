import InitECandidate.Runtime.PtSegBaseGD
import InitECandidate.Runtime.PtKoWsLGD
import InitECandidate.Runtime.RecFrameGDL
/-!
Base of the actual `process_transaction` segment from `te_new` (spine drop 34) to `process_message_call`: the segment
state `SI` at the fresh base `Lo` (the heap pointer at drop 34) with its conversions from and to `PXR`, the memory steps
keeping it (writes at or above `Lo`, the Keccak state/pad windows), a word store at or above `Lo` whose normal outcome
learns the address is in the domain, the conjunction of two triples on one program, and lowering a heap-aware triple
proven at the current heap pointer as arena bound.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString



section si
variable {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n} {D : BitVec 64 → Prop} {B : Bool}
  {Excl : BitVec 64 → Prop} {Lo Nj H0 : BitVec 64} {M0 : Mem}





/-- Memory changes at or above `Lo` and in the Keccak state/pad windows keep `SI` (the registry cells, headers and
`ko` arrays and every outside word are off the workspace). -/
theorem si_kpL {SP0 FM K Pd NB P0 : BitVec 64} {M M' : Mem} {G : GA}
    (safe : ∀ x, (∃ i, x = c i ∨ HdrR (T i) x) → WsSafe SP0 FM K Pd NB x)
    (hOutSafe : ∀ x, Out x → WsSafe SP0 FM K Pd NB x ∧ x.toNat < P0.toNat)
    (hkoWs : KoWsL SP0 FM K Pd NB (T ko))
    (h : SI n c T Out ko D B Excl Lo Nj M0 M G) (keep : ∀ x, x.toNat < Lo.toNat → ¬ KPW K Pd x → M' x = M x) :
    SI n c T Out ko D B Excl Lo Nj M0 M' G := by
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
    exact (keep x (regT_out_lt reg ho) hnk).trans (fr x ho hx)

end si

section st
variable {D : BitVec 64 → Prop} {B : Bool} {A : GA → Prop} {w : BitVec 64} {Vn : MlS → Prop}
  {RR : ValueHOL 64 → Mem → GA → Prop}
  {n : Nat} {c T : Fin n → BitVec 64} {Out : BitVec 64 → Prop} {ko : Fin n}
  {Excl : BitVec 64 → Prop} {Lo Nj : BitVec 64} {M0 : Mem}




end st

section lw
variable {SP0 P0 FM w : BitVec 64} {G0 : GA} {Vn : MlS → Prop}


end lw
end InitECandidate.Runtime
