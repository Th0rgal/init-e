import InitECandidate.Runtime.HashFindEnvironment32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The hash call's preserved memory and new h local leave every lookup-table
condition intact, including the actual byte-based occupancy count. -/
theorem HashFindEnvironment32.after_hash {F : Type} (keys stride key capacity used hash : BitVec 64)
    (state post : PanSemStateFiniteExact 64 F)
    (ready : HashFindEnvironment32 keys stride key capacity used state)
    (memory : post.memory = state.memory) (code : post.code = state.code)
    (addresses : post.memaddrs = state.memaddrs) (endian : post.be = state.be)
    (locals : post.locals = (setVarHOLFinite (ofString "h") (.val (.word hash)) state).locals) :
    HashFindEnvironment32 keys stride key capacity used post := by
  have other : ∀ name, name ≠ ofString "h" → post.locals.lookup name = state.locals.lookup name := by
    intro name different
    rw [locals]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  refine ⟨code.trans ready.code,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [other _ (by decide)]; exact ready.keysLocal
  · rw [other _ (by decide)]; exact ready.strideLocal
  · rw [other _ (by decide)]; exact ready.keyLocal
  · rw [other _ (by decide)]; exact ready.lengthLocal
  · rw [other _ (by decide)]; exact ready.capLocal
  · rw [other _ (by decide)]; exact ready.usedLocal
  · rw [addresses]; exact ready.arrayDomain
  · rw [addresses]; exact ready.keyDomain
  · rw [memory,addresses,endian]; exact ready.readable
  · have reads : hashOccupancyRead post used = hashOccupancyRead state used := by
      funext index
      unfold hashOccupancyRead
      rw [memory,addresses,endian]
    rw [reads]; exact ready.room

#print axioms HashFindEnvironment32.after_hash
end InitECandidate.Runtime
