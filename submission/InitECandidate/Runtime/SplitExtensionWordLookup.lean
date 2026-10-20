import InitECandidate.Runtime.OriginalSplitExtensionCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Exact original six-word extension splitter bindings, including the
actual common-prefix argument and original installed function body. -/
theorem original_split_extension_word_lookup
 (node key length value valueLength matched : BitVec 64) :
 lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "_split_extension")
 [.val (.word node),.val (.word key),.val (.word length),.val (.word value),.val (.word valueLength),.val (.word matched)]=some (sourceFunctionBody Guest.guestFn__split_extension,
 ((((((HolFiniteMapExact.empty.update (ofString "node",.val (.word node))).update (ofString "rk",.val (.word key))).update (ofString "rl",.val (.word length))).update (ofString "vptr",.val (.word value))).update (ofString "vlen",.val (.word valueLength))).update (ofString "pl",.val (.word matched))),.one) := by
 have raw : lookupCodeHOLExact originalRuntimeCode.lookup (ofString "_split_extension")
  [.val (.word node),.val (.word key),.val (.word length),.val (.word value),.val (.word valueLength),.val (.word matched)]=some (sourceFunctionBody Guest.guestFn__split_extension,
  (fun current=>if current=ofString "pl" then some (.val (.word matched)) else if current=ofString "vlen" then some (.val (.word valueLength)) else if current=ofString "vptr" then some (.val (.word value)) else if current=ofString "rl" then some (.val (.word length)) else if current=ofString "rk" then some (.val (.word key)) else if current=ofString "node" then some (.val (.word node)) else none),.one) := by
  simp (config:={decide:=true}) [lookupCodeHOLExact,originalRuntimeCode_splitExtension_lookup,shapeOfHOLExact,shapeEqHOL]
 unfold Flapjack.PanSemStateFiniteExact.lookupCodeHOLFinite
 split
 · rename_i missing
   rw [raw] at missing
   cases missing
 · rename_i foundBody foundLocals foundShape found
   have equal:=Option.some.inj (found.symm.trans raw)
   obtain ⟨rfl,rest⟩:=Prod.mk.inj equal
   obtain ⟨rfl,rfl⟩:=Prod.mk.inj rest
   apply congrArg (fun locals=>some (sourceFunctionBody Guest.guestFn__split_extension,locals,ShapeHOL.one))
   apply HolFiniteMapExact.ext
   funext key
   by_cases case0 : key=ofString "pl"
   · subst key
     simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
   · 
     by_cases case1 : key=ofString "vlen"
     · subst key
       simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
     · 
       by_cases case2 : key=ofString "vptr"
       · subst key
         simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
       · 
         by_cases case3 : key=ofString "rl"
         · subst key
           simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
         · 
           by_cases case4 : key=ofString "rk"
           · subst key
             simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
           · 
             by_cases case5 : key=ofString "node"
             · subst key
               simp (config:={decide:=true}) [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY]
             · simp [HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,FEMPTY,case0,case1,case2,case3,case4,case5,Ne.symm case0,Ne.symm case1,Ne.symm case2,Ne.symm case3,Ne.symm case4,Ne.symm case5]

#print axioms original_split_extension_word_lookup
end InitECandidate.Runtime
