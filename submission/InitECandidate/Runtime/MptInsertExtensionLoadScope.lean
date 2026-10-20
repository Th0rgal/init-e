import InitECandidate.Runtime.MptInsertExtensionDispatchBound
import InitECandidate.Runtime.MptInsertNodeLoad
import InitECandidate.Runtime.PanDecNormalScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertExtensionLoadedState {F : Type} (s : PanSemStateFiniteExact 64 F)
 (segment length : BitVec 64) : PanSemStateFiniteExact 64 F :=
 setVarHOLFinite (ofString "sl") (.val (.word length))
  (setVarHOLFinite (ofString "seg") (.val (.word segment)) s)

/-- Normal completion of the original extension dispatch earns both actual
field reads and reaches the comparison without consuming clock. The two
lexical restorations are recorded exactly, including previously absent locals. -/
theorem mpt_insert_extension_loads_normal_scope {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (node : BitVec 64)
 (atNode : s.locals.lookup (ofString "node")=some (.val (.word node)))
 (run : evaluateHOLFiniteState s mptInsertExtensionDispatch=(none,post)) :
 ∃segment length : BitVec 64,∃output : PanSemStateFiniteExact 64 F,
 s.memory (node+32#64)=.word segment ∧s.memory (node+40#64)=.word length ∧
 s.memaddrs (node+32#64) ∧s.memaddrs (node+40#64) ∧
 evaluateHOLFiniteState (mptInsertExtensionLoadedState s segment length)
  mptInsertExtensionComparison=(none,output) ∧
 post={output with locals:=(HolFiniteMapExact.resVarEq
  (HolFiniteMapExact.resVarEq output.locals (ofString "sl",
   (setVarHOLFinite (ofString "seg") (.val (.word segment)) s).locals.lookup (ofString "sl")))
  (ofString "seg",s.locals.lookup (ofString "seg")))} := by
 rw [source_mptInsert_extension_dispatch] at run
 obtain ⟨segValue,firstOutput,segEval,firstRun,firstScope⟩:=
  evaluate_dec_normal_scope s post (ofString "seg") .one _ _ run
 obtain ⟨segment,segEq,segmentField,segmentDomain⟩:=mpt_insert_node_load_word s node 32 segValue atNode segEval
 subst segValue
 let first:=setVarHOLFinite (ofString "seg") (.val (.word segment)) s
 change evaluateHOLFiniteState first _=(none,firstOutput) at firstRun
 have firstNode : first.locals.lookup (ofString "node")=some (.val (.word node)) := by
  simpa (config:={decide:=true}) [first,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atNode
 obtain ⟨slValue,output,slEval,comparisonRun,secondScope⟩:=
  evaluate_dec_normal_scope first firstOutput (ofString "sl") .one _ _ firstRun
 obtain ⟨length,slEq,lengthField,lengthDomain⟩:=mpt_insert_node_load_word first node 40 slValue firstNode slEval
 subst slValue
 refine ⟨segment,length,output,segmentField,lengthField,segmentDomain,lengthDomain,comparisonRun,?_⟩
 rw [firstScope,secondScope]

/-- The loaded comparison state changes only its two lexical locals. -/
theorem mpt_insert_extension_loaded_local {F : Type} (s : PanSemStateFiniteExact 64 F)
 (segment length : BitVec 64) (name : MlS)
 (notSegment : name≠ofString "seg") (notLength : name≠ofString "sl") :
 (mptInsertExtensionLoadedState s segment length).locals.lookup name=s.locals.lookup name := by
 simp [mptInsertExtensionLoadedState,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
  notSegment,notLength,Ne.symm notSegment,Ne.symm notLength]

#print axioms mpt_insert_extension_loads_normal_scope
#print axioms mpt_insert_extension_loaded_local
end InitECandidate.Runtime
