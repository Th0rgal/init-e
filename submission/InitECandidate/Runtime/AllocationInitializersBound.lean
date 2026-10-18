import InitECandidate.Runtime.AllocationFragmentBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def structuralFunctionBody (declaration : Decl (BitVec 64)) : ProgHOL 64 :=
  match InitECandidate.Proofs.FrontendCodecComputation.declToHOLStructural declaration with
  | .function function => function.body
  | _ => .skip

theorem sourceFunctionBody_eq_structural (declaration : Decl (BitVec 64)) :
    sourceFunctionBody declaration = structuralFunctionBody declaration := by
  unfold sourceFunctionBody structuralFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

def sha256InitFragment : AllocationFragment (structuralFunctionBody Guest.guestFn_sha256_init) := by
  repeat first
    | exact AllocationFragment.straight _ (by decide)
    | apply AllocationFragment.sequence
    | apply AllocationFragment.conditional
    | exact AllocationFragment.allocation _ _

theorem sha256InitFragment_cost : sha256InitFragment.cost = 6 := by rfl

theorem evaluate_sha256Init_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 6 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_sha256_init)
    state.clock ≤ result.2.clock + 6 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  rw [sourceFunctionBody_eq_structural]
  simpa only [sha256InitFragment_cost] using sha256InitFragment.bounded state code
    (by simpa only [sha256InitFragment_cost] using budget)

#print axioms evaluate_sha256Init_body_bounded

def keccakInitFragment : AllocationFragment (structuralFunctionBody Guest.guestFn_keccak_init) := by
  repeat first
    | exact AllocationFragment.straight _ (by decide)
    | apply AllocationFragment.sequence
    | apply AllocationFragment.conditional
    | exact AllocationFragment.allocation _ _

theorem keccakInitFragment_cost : keccakInitFragment.cost = 4 := by rfl

theorem evaluate_keccakInit_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 4 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak_init)
    state.clock ≤ result.2.clock + 4 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  rw [sourceFunctionBody_eq_structural]
  simpa only [keccakInitFragment_cost] using keccakInitFragment.bounded state code
    (by simpa only [keccakInitFragment_cost] using budget)

#print axioms evaluate_keccakInit_body_bounded

def sszInitFragment : AllocationFragment (structuralFunctionBody Guest.guestFn_ssz_init) := by
  repeat first
    | exact AllocationFragment.straight _ (by decide)
    | apply AllocationFragment.sequence
    | apply AllocationFragment.conditional
    | exact AllocationFragment.allocation _ _

theorem sszInitFragment_cost : sszInitFragment.cost = 6 := by rfl

theorem evaluate_sszInit_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 6 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ssz_init)
    state.clock ≤ result.2.clock + 6 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  rw [sourceFunctionBody_eq_structural]
  simpa only [sszInitFragment_cost] using sszInitFragment.bounded state code
    (by simpa only [sszInitFragment_cost] using budget)

#print axioms evaluate_sszInit_body_bounded

def u256WsInitFragment : AllocationFragment (structuralFunctionBody Guest.guestFn_u256_ws_init) := by
  repeat first
    | exact AllocationFragment.straight _ (by decide)
    | apply AllocationFragment.sequence
    | apply AllocationFragment.conditional
    | exact AllocationFragment.allocation _ _

theorem u256WsInitFragment_cost : u256WsInitFragment.cost = 2 := by rfl

theorem evaluate_u256WsInit_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 2 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_u256_ws_init)
    state.clock ≤ result.2.clock + 2 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  rw [sourceFunctionBody_eq_structural]
  simpa only [u256WsInitFragment_cost] using u256WsInitFragment.bounded state code
    (by simpa only [u256WsInitFragment_cost] using budget)

#print axioms evaluate_u256WsInit_body_bounded

def ripemd160InitFragment : AllocationFragment (structuralFunctionBody Guest.guestFn_ripemd160_init) := by
  repeat first
    | exact AllocationFragment.straight _ (by decide)
    | apply AllocationFragment.sequence
    | apply AllocationFragment.conditional
    | exact AllocationFragment.allocation _ _

theorem ripemd160InitFragment_cost : ripemd160InitFragment.cost = 8 := by rfl

theorem evaluate_ripemd160Init_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 8 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ripemd160_init)
    state.clock ≤ result.2.clock + 8 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  rw [sourceFunctionBody_eq_structural]
  simpa only [ripemd160InitFragment_cost] using ripemd160InitFragment.bounded state code
    (by simpa only [ripemd160InitFragment_cost] using budget)

#print axioms evaluate_ripemd160Init_body_bounded

def blake2InitFragment : AllocationFragment (structuralFunctionBody Guest.guestFn_blake2_init) := by
  repeat first
    | exact AllocationFragment.straight _ (by decide)
    | apply AllocationFragment.sequence
    | apply AllocationFragment.conditional
    | exact AllocationFragment.allocation _ _

theorem blake2InitFragment_cost : blake2InitFragment.cost = 6 := by rfl

theorem evaluate_blake2Init_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 6 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_blake2_init)
    state.clock ≤ result.2.clock + 6 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut := by
  rw [sourceFunctionBody_eq_structural]
  simpa only [blake2InitFragment_cost] using blake2InitFragment.bounded state code
    (by simpa only [blake2InitFragment_cost] using budget)

#print axioms evaluate_blake2Init_body_bounded

end InitECandidate.Runtime
