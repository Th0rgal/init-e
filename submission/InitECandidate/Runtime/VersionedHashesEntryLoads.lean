import InitECandidate.Runtime.VersionedHashesLoopSource
import InitECandidate.Runtime.HeaderLoadScope
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def versionedHashesLoadedState {F : Type} (state : PanSemStateFiniteExact 64 F)
    (payload array count vh hashCount : BitVec 64) : PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "nvh") (.val (.word hashCount))
    (setVarHOLFinite (ofString "vh") (.val (.word vh))
      (setVarHOLFinite (ofString "ntx") (.val (.word count))
        (setVarHOLFinite (ofString "txs") (.val (.word array))
          (setVarHOLFinite (ofString "pl") (.val (.word payload)) state))))

theorem source_versioned_hashes_entry_loads : sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes =
    .dec (ofString "pl") .one (.load .one (hashLocalAddress (ofString "si") 0))
      (.dec (ofString "txs") .one (.load .one (hashLocalAddress (ofString "pl") 32))
        (.dec (ofString "ntx") .one (.load .one (hashLocalAddress (ofString "pl") 40))
          (.dec (ofString "vh") .one (.load .one (hashLocalAddress (ofString "si") 8))
            (.dec (ofString "nvh") .one (.load .one (hashLocalAddress (ofString "si") 16)) (versionedHashesAt 5))))) := by
  simp only [versionedHashesAt,authorizationNext,sourceFunctionBody,hashLocalAddress,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem versioned_hashes_entry_loads_clock {F : Type} (state : PanSemStateFiniteExact 64 F)
    (si payload array count vh hashCount : BitVec 64)
    (siLocal : state.locals.lookup (ofString "si") = some (.val (.word si)))
    (payloadDomain : state.memaddrs (si + 0)) (payloadCell : state.memory (si + 0) = .word payload)
    (arrayDomain : state.memaddrs (payload + 32)) (arrayCell : state.memory (payload + 32) = .word array)
    (countDomain : state.memaddrs (payload + 40)) (countCell : state.memory (payload + 40) = .word count)
    (vhDomain : state.memaddrs (si + 8)) (vhCell : state.memory (si + 8) = .word vh)
    (hashCountDomain : state.memaddrs (si + 16)) (hashCountCell : state.memory (si + 16) = .word hashCount) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes)).1 =
      (evaluateHOLFiniteState (versionedHashesLoadedState state payload array count vh hashCount) (versionedHashesAt 5)).1 ∧
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes)).2.clock =
      (evaluateHOLFiniteState (versionedHashesLoadedState state payload array count vh hashCount) (versionedHashesAt 5)).2.clock := by
  let s1 := setVarHOLFinite (ofString "pl") (.val (.word payload)) state
  let s2 := setVarHOLFinite (ofString "txs") (.val (.word array)) s1
  let s3 := setVarHOLFinite (ofString "ntx") (.val (.word count)) s2
  let s4 := setVarHOLFinite (ofString "vh") (.val (.word vh)) s3
  have pl1 : s1.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    simp [s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have pl2 : s2.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    simp [s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "txs" ≠ ofString "pl" by decide]
  have si3 : s3.locals.lookup (ofString "si") = some (.val (.word si)) := by
    simpa [s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vh" ≠ ofString "si" by decide,show ofString "ntx" ≠ ofString "si" by decide,show ofString "txs" ≠ ofString "si" by decide,show ofString "pl" ≠ ofString "si" by decide] using siLocal
  have si4 : s4.locals.lookup (ofString "si") = some (.val (.word si)) := by
    simpa [s4,s3,s2,s1,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "vh" ≠ ofString "si" by decide,show ofString "ntx" ≠ ofString "si" by decide,show ofString "txs" ≠ ofString "si" by decide,show ofString "pl" ≠ ofString "si" by decide] using siLocal
  rw [source_versioned_hashes_entry_loads,
    evaluate_header_load_scope state (ofString "pl") (ofString "si") si 0 payload _ siLocal payloadDomain payloadCell,
    evaluate_header_load_scope s1 (ofString "txs") (ofString "pl") payload 32 array _ pl1 arrayDomain arrayCell,
    evaluate_header_load_scope s2 (ofString "ntx") (ofString "pl") payload 40 count _ pl2 countDomain countCell,
    evaluate_header_load_scope s3 (ofString "vh") (ofString "si") si 8 vh _ si3 vhDomain vhCell,
    evaluate_header_load_scope s4 (ofString "nvh") (ofString "si") si 16 hashCount _ si4 hashCountDomain hashCountCell]
  exact ⟨rfl,rfl⟩

#print axioms versioned_hashes_entry_loads_clock
end InitECandidate.Runtime
