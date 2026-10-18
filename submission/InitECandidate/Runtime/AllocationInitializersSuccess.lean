import InitECandidate.Runtime.GlobalAllocationPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def sha256InitAllocations : List (MlS × BitVec 64) := [(ofString "sha_st",64),(ofString "sha_pad",128),(ofString "sha_accel",96)]

theorem source_sha256Init_allocations : sourceFunctionBody Guest.guestFn_sha256_init =
    globalAllocationProgram sha256InitAllocations (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_sha256Init_body_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (words : ∀ entry ∈ sha256InitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (sha256InitAllocations.map Prod.snd))
    (budget : 3 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_sha256_init) =
        (some (.returned (.val (.word 0))),post) ∧
      post.clock = state.clock - 3 ∧ post.memory = state.memory ∧
      post.locals = HolFiniteMapExact.empty ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer sha256InitAllocations ∧
      post.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationPlanEnd pointer (sha256InitAllocations.map Prod.snd)))) := by
  rw [source_sha256Init_allocations]
  exact evaluate_globalAllocation_return state sha256InitAllocations pointer code heap
    (by decide) words safe budget

#print axioms source_sha256Init_allocations
#print axioms evaluate_sha256Init_body_success

def keccakInitAllocations : List (MlS × BitVec 64) := [(ofString "keccak_st",200),(ofString "keccak_pad",136)]

theorem source_keccakInit_allocations : sourceFunctionBody Guest.guestFn_keccak_init =
    globalAllocationProgram keccakInitAllocations (.return (.const 0)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_keccakInit_body_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (words : ∀ entry ∈ keccakInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (keccakInitAllocations.map Prod.snd))
    (budget : 2 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_keccak_init) =
        (some (.returned (.val (.word 0))),post) ∧
      post.clock = state.clock - 2 ∧ post.memory = state.memory ∧
      post.locals = HolFiniteMapExact.empty ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer keccakInitAllocations ∧
      post.globals.lookup (ofString "heap_ptr") =
        some (.val (.word (allocationPlanEnd pointer (keccakInitAllocations.map Prod.snd)))) := by
  rw [source_keccakInit_allocations]
  exact evaluate_globalAllocation_return state keccakInitAllocations pointer code heap
    (by decide) words safe budget

#print axioms source_keccakInit_allocations
#print axioms evaluate_keccakInit_body_success

end InitECandidate.Runtime
