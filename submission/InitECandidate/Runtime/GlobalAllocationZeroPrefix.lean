import InitECandidate.Runtime.GlobalAllocationPrefix
import InitECandidate.Runtime.MemzeroAlignedCall
import InitECandidate.Runtime.MemzeroIntervalDomains
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual global allocation followed by zeroing reaches its unrestricted
continuation. Only the allocated interval must be accessible. -/
theorem evaluate_globalAllocation_zero_prefix {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (pointer size old : BitVec 64) (tail : ProgHOL 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (slot : state.globals.lookup name = some (.val (.word old)))
    (different : name ≠ ofString "heap_ptr")
    (safe : AllocationPlanSafe pointer [size])
    (aligned : pointer.toNat % 8 = 0)
    (small : pointer.toNat + size.toNat ≤ 33806089496)
    (arena : ∀ address : BitVec 64, pointer.toNat ≤ address.toNat →
      address.toNat < pointer.toNat + size.toNat → state.memaddrs address)
    (budget : size.toNat + 2 ≤ state.clock) :
    ∃ next : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (globalAllocationProgram [(name,size)]
        (.seq (.call (some (none,none)) (ofString "memzero") [.var .global name,.const size]) tail)) =
        evaluateHOLFiniteState next tail ∧
      state.clock ≤ next.clock + (size.toNat + 2) ∧ next.clock ≤ state.clock ∧
      next.code = state.code ∧ next.memaddrs = state.memaddrs ∧ next.locals = state.locals ∧
      next.globals = globalAllocationGlobals state.globals pointer [(name,size)] ∧
      ZeroBytePrefix next pointer size.toNat := by
  obtain ⟨ready,run,clock,_,locals,installed,domain,globals,_⟩ :=
    evaluate_globalAllocation_prefix state [(name,size)]
      (.seq (.call (some (none,none)) (ofString "memzero") [.var .global name,.const size]) tail)
      pointer code heap
      (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact different)
      (by intro entry member; simp only [List.mem_singleton] at member; subst entry; exact ⟨old,slot⟩)
      safe (by simp; omega)
  have destination : ready.globals.lookup name = some (.val (.word pointer)) := by
    rw [globals]
    simp [globalAllocationGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  have arguments : evalListHOLFinite ready
      (h := fun a => Classical.propDecidable (ready.memaddrs a)) [.var .global name,.const size] =
        some [.val (.word pointer),.val (.word size)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,lookupKvarHOLExact,destination]
  have domains := memzero_interval_domains ready pointer size aligned (by omega)
    (by intro address lower upper; rw [domain]; exact arena address lower upper)
  obtain ⟨next,zero,covered,cost,remaining,retGlobals,retCode,retDomain,_,retLocals,_⟩ :=
    evaluate_memzero_aligned_call ready (.var .global name) (.const size) pointer size
      arguments (installed.trans code) (by simp only [List.length_cons,List.length_nil] at clock; omega)
      small aligned domains.1 domains.2
  refine ⟨next,?_,?_,?_,retCode.trans installed,retDomain.trans domain,
    retLocals.trans locals,retGlobals.trans globals,covered⟩
  · rw [run,evaluateHOLFiniteState_seq_line780,zero]
  · simp only [List.length_cons,List.length_nil] at clock
    omega
  · simp only [List.length_cons,List.length_nil] at clock
    omega

#print axioms evaluate_globalAllocation_zero_prefix
end InitECandidate.Runtime
