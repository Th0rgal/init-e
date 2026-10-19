import InitECandidate.Runtime.AccountOptionalArena
import InitECandidate.Runtime.HtabReadOnly
import InitECandidate.Proofs.AllocationFacts
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {SP0 P0 FM w : BitVec 64} {G0 : HolFiniteMapExact MlS (ValueHOL 64)}

/-- The actual source memory domain satisfies the arena domain bound. -/
theorem domOK_ordinaryDomain : DomOK ordinaryDomain := by
  intro a h
  have := InitE.ordinaryDomain_below_top a h
  have e : heapEnd < 2^62 := by
    norm_num [heapEnd,stackStart,ramEnd,ramStart,ramSize,stackSize,globalsWords]
  omega

/-- Every state reached from the source initial state keeps the source domain, hence the bound. -/
theorem domOK_of_memaddrs {F : Type} (s : PanSemStateFiniteExact 64 F) (h : s.memaddrs = ordinaryDomain) :
    DomOK s.memaddrs := h ▸ domOK_ordinaryDomain

/-- `htab_get` is an arena-safe callee (read-only). -/
theorem htabGet_acallee : ACallee SP0 P0 FM G0 w (sourceFunctionBody Guest.guestFn_htab_get) :=
  acallee_of_asafe (asafe_mf htabGet_memoryFrame)

#print axioms domOK_ordinaryDomain
#print axioms htabGet_acallee
end InitECandidate.Runtime
