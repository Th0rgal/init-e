import InitECandidate.Runtime.PtKoWsLGD
import InitECandidate.Runtime.FirstSixInitializerLayout
/-!
The workspace floor from the actual initializer. `firstSixInitializerGlobals` (root's exact initializer globals) places
the nibble scratch at `2713717520` (64 bytes); with the keccak state `2713714976` (200 bytes), the padding `2713715176`
(136 bytes), the secp scratch `2713718280` (448 bytes) and the scratch arena top `2713714688`, every workspace word lies
below the final initializer heap `L0 = 2713731432`. A valid table layout places every table word at or above its header
(`intabf_ge_of_ok`), so a table whose header is at or above `L0` avoids every workspace at its current layout.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual nibble scratch from the initializer. -/
theorem firstSixInitializerGlobals_nib (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (firstSixInitializerGlobals globals).lookup (ofString "mpt_nib_scratch") = some (.val (.word 2713717520)) := by
  simp [firstSixInitializerGlobals,firstFourInitializerGlobals,globalAllocationGlobals,
    sha256InitAllocations,keccakInitAllocations,sszInitAllocations,mptInitAllocations,u256WorkspaceAllocations,
    HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  decide

/-- Layout validity: every word of a validly laid-out table at `Tt` is at or above the header. -/
theorem intabf_ge_of_ok {lo : TLay} {Tt Hx x : BitVec 64} (ok : lo.ok Tt Hx)
    (hx : InTabF Tt lo.KS lo.SD lo.C lo.US lo.VS lo.OS lo.OPS x) : Tt.toNat ≤ x.toNat := by
  have k := ok.keysR.1; have v := ok.valsR.1; have u := ok.usedR.1; have o := ok.orderR.1; have op := ok.oposR.1
  rcases hx with ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ | ⟨h,_⟩ <;> omega

/-- The concrete workspace floor. -/
theorem wsSafe_floor {SP0 FM : BitVec 64} (hSP : SP0.toNat ≤ 2713714688) (x : BitVec 64)
    (hx : 2713731432 ≤ x.toNat) : WsSafe SP0 FM 2713714976#64 2713715176#64 2713717520#64 x :=
  wsSafe_of_low (L0 := 2713731432#64) (by simp; omega) (by decide) (by decide) (by decide) x (by simpa using hx)

/-- The concrete secp-scratch floor. -/
theorem scWin_floor (x : BitVec 64) (hx : 2713731432 ≤ x.toNat) : ¬ MWin 2713718280#64 448 x := by
  intro ⟨j,hj,h⟩
  have e : (2713718280#64 + BitVec.ofNat 64 j).toNat = 2713718280 + j := by
    rw [BitVec.toNat_add_of_lt] <;> simp <;> omega
  rcases h with rfl | rfl
  · rw [e] at hx; omega
  · rw [byteAlign_toNat,e] at hx
    have := Nat.div_mul_le_self (2713718280 + j) 8
    omega

/-- The repaired table premises for a table with header at or above the floor. -/
theorem koWsL_floor {SP0 FM Tt : BitVec 64} (hSP : SP0.toNat ≤ 2713714688) (hT : 2713731432 ≤ Tt.toNat) :
    KoWsL SP0 FM 2713714976#64 2713715176#64 2713717520#64 Tt :=
  koWsL_of_low (L0 := 2713731432#64) (fun x hx => wsSafe_floor hSP x (by simpa using hx)) (by simpa using hT)

theorem koSc_floor {Tt : BitVec 64} (hT : 2713731432 ≤ Tt.toNat) :
    TabAvoid (fun x => ¬ MWin 2713718280#64 448 x) Tt :=
  tabAvoid_of_low (L0 := 2713731432#64) (fun x hx => scWin_floor x (by simpa using hx)) (by simpa using hT)

#print axioms firstSixInitializerGlobals_nib
#print axioms intabf_ge_of_ok
#print axioms wsSafe_floor
#print axioms scWin_floor
#print axioms koWsL_floor
#print axioms koSc_floor
end InitECandidate.Runtime
