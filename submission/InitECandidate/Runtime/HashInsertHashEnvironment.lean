import InitECandidate.Runtime.HashInsertIndexScope
import InitECandidate.Runtime.HashCall32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A memory-preserving hash call and its h binding retain all shared
insertion premises, including header/count agreement and slot separation. -/
theorem HashInsertSlotEnvironment.after_hash {F : Type}
    (capacity used table values value order orderPos count hash : BitVec 64)
    (state post : PanSemStateFiniteExact 64 F)
    (environment : HashInsertSlotEnvironment capacity used table values value order orderPos count state)
    (memory : post.memory = state.memory) (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (locals : post.locals = (setVarHOLFinite (ofString "h") (.val (.word hash)) state).locals) :
    HashInsertSlotEnvironment capacity used table values value order orderPos count post := by
  have other : ∀ name, name ≠ ofString "h" → post.locals.lookup name = state.locals.lookup name := by
    intro name different
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
    funext index
    unfold hashOccupancyRead
    rw [memory,addresses,endian]
  refine {
    tableLocal := by rw [other _ (by decide)]; exact environment.tableLocal
    orderLocal := by rw [other _ (by decide)]; exact environment.orderLocal
    orderPosLocal := by rw [other _ (by decide)]; exact environment.orderPosLocal
    usedLocal := by rw [other _ (by decide)]; exact environment.usedLocal
    valueLocal := by rw [other _ (by decide)]; exact environment.valueLocal
    valuesDomain := by rw [addresses]; exact environment.valuesDomain
    valuesMemory := by rw [memory]; exact environment.valuesMemory
    valueDomain := by rw [addresses]; exact environment.valueDomain
    byteDomain := by rw [addresses]; exact environment.byteDomain
    orderDomain := by rw [addresses]; exact environment.orderDomain
    orderPosDomain := by rw [addresses]; exact environment.orderPosDomain
    countDomain := by rw [addresses]; exact environment.countDomain
    countMemory := by rw [memory]; exact environment.countMemory
    agreement := by rw [reads]; exact environment.agreement
    noWrap := environment.noWrap
    valueCountSeparate := environment.valueCountSeparate
    valueSeparate := environment.valueSeparate
    separate := environment.separate
  }

#print axioms HashInsertSlotEnvironment.after_hash
end InitECandidate.Runtime
