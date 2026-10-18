import InitECandidate.Runtime.Bn254InitCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxHeartbeats 4000000

/-- The fifteen globals written by the first bn254_init (besides heap_ptr). -/
def bn254InitNames : List MlS :=
  bn254AccelNames ++ [ofString "bn_gamma",ofString "bn_b2",ofString "bn_expw"]

theorem bn254InitGlobals_heap (g : HolFiniteMapExact MlS (ValueHOL 64)) (H : BitVec 64) :
    (bn254InitGlobals g H).lookup (ofString "heap_ptr") = some (.val (.word (H + 1216))) := by
  have e : ofString "bn_expw" ≠ ofString "heap_ptr" := by decide
  simp [bn254InitGlobals,HolFiniteMapExact.lookup_update,FUPDATE,e]

theorem bn254InitGlobals_other (g : HolFiniteMapExact MlS (ValueHOL 64)) (H : BitVec 64) (watched : MlS)
    (notHeap : watched ≠ ofString "heap_ptr") (notWritten : watched ∉ bn254InitNames) :
    (bn254InitGlobals g H).lookup watched = g.lookup watched := by
  simp only [bn254InitNames,bn254AccelNames,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,not_or] at notWritten
  obtain ⟨⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12⟩,b1,b2,b3⟩ := notWritten
  simp [bn254InitGlobals,bn254AccelGlobals,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap,
    Ne.symm a1,Ne.symm a2,Ne.symm a3,Ne.symm a4,Ne.symm a5,Ne.symm a6,Ne.symm a7,Ne.symm a8,Ne.symm a9,
    Ne.symm a10,Ne.symm a11,Ne.symm a12,Ne.symm b1,Ne.symm b2,Ne.symm b3]

/-- First bn254_init at the actual entry heap 2713718728 reached after the first
seven main initializers: at most 35 ticks, never a timeout, and on normal
continuation heap_ptr = 2713719944 with exactly the BN254 globals installed. -/
theorem evaluate_bn254Init_call_at_entry_heap {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713718728)))
    (gammaZero : state.globals.lookup (ofString "bn_gamma") = some (.val (.word 0)))
    (paramsZero : state.globals.lookup (ofString "bn_accel_params") = some (.val (.word 0)))
    (words : ∀ name ∈ bn254AccelNames, ∃ word : BitVec 64, state.globals.lookup name = some (.val (.word word)))
    (b2Word : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_b2") = some (.val (.word word)))
    (expwWord : ∃ word : BitVec 64, state.globals.lookup (ofString "bn_expw") = some (.val (.word word)))
    (arena : ∀ address : BitVec 64, 2713718728 ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (budget : 35 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "bn254_init") [])
    state.clock ≤ result.2.clock + 35 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = bn254InitGlobals state.globals 2713718728 ∧
        result.2.globals.lookup (ofString "heap_ptr") = some (.val (.word 2713719944)) ∧
        result.2.locals = state.locals ∧ result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs) := by
  obtain ⟨a,b,c,d⟩ := evaluate_bn254Init_call_outcome state 2713718728 code heap (by decide) (by decide) (by decide)
    gammaZero paramsZero words b2Word expwWord (fun x lo hi => arena x (by simpa using lo) hi) budget
  refine ⟨a,b,c,fun normal => ?_⟩
  obtain ⟨g,l,k,m⟩ := d normal
  refine ⟨g,?_,l,k,m⟩
  rw [g,bn254InitGlobals_heap]
  rfl

#print axioms bn254InitGlobals_other
#print axioms evaluate_bn254Init_call_at_entry_heap
end InitECandidate.Runtime
