import InitECandidate.Runtime.OriginalMptInsertCode
import InitECandidate.Runtime.MptInsertIndexedBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def mptInsertCalleeLocals (node key length level valuePointer valueLength : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64):=
 (((((HolFiniteMapExact.empty.update (ofString "node",.val (.word node))).update
  (ofString "key",.val (.word key))).update (ofString "klen",.val (.word length))).update
  (ofString "level",.val (.word level))).update (ofString "vptr",.val (.word valuePointer))).update
  (ofString "vlen",.val (.word valueLength))

/-- Exact binding of the actual installed original insertion body and its six
word arguments, rather than an assumed callee contract. -/
theorem mpt_insert_indexed_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
 (node key length level valuePointer valueLength : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "_mpt_insert_node")
  [.val (.word node),.val (.word key),.val (.word length),.val (.word level),.val (.word valuePointer),.val (.word valueLength)]=
 some (sourceFunctionBody Guest.guestFn__mpt_insert_node,mptInsertCalleeLocals node key length level valuePointer valueLength,.one) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,originalRuntimeCode_mptInsert_lookup,shapeOfHOLExact,shapeEqHOL]
 funext name
 by_cases six : name=ofString "vlen"
 · subst name;simp (config:={decide:=true}) [mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · by_cases five : name=ofString "vptr"
   · subst name;simp (config:={decide:=true}) [mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
   · by_cases four : name=ofString "level"
     · subst name;simp (config:={decide:=true}) [mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
     · by_cases three : name=ofString "klen"
       · subst name;simp (config:={decide:=true}) [mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
       · by_cases two : name=ofString "key"
         · subst name;simp (config:={decide:=true}) [mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
         · by_cases one : name=ofString "node"
           · subst name;simp (config:={decide:=true}) [mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE]
           · simp [mptInsertCalleeLocals,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
              one,two,three,four,five,six,Ne.symm one,Ne.symm two,Ne.symm three,Ne.symm four,Ne.symm five,Ne.symm six]

#print axioms mpt_insert_indexed_lookup
end InitECandidate.Runtime
