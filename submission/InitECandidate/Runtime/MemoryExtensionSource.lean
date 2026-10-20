import InitECandidate.Runtime.FrameNewSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memoryExtensionAt (index : Nat) : ProgHOL 64:= (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_extend_memory)
def memoryExtensionGrowthAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (match memoryExtensionAt 4 with | .seq (.ite _ branch _) _=>branch | _=>.skip)

theorem source_memory_extension_0 : memoryExtensionAt 0=.seq (.ite (.cmp .equal (.var .local (ofString "expand_by")) (.const 0)) (.return (.const 0)) .skip) (memoryExtensionAt 1):=rfl
theorem source_memory_extension_1 : memoryExtensionAt 1=.dec (ofString "len") .one (.load .one (fundingAddress 32)) (memoryExtensionAt 2):=rfl
theorem source_memory_extension_2 : memoryExtensionAt 2=.dec (ofString "cap") .one (.load .one (fundingAddress 40)) (memoryExtensionAt 3):=rfl
theorem source_memory_extension_3 : memoryExtensionAt 3=.dec (ofString "nlen") .one (.op .add [.var .local (ofString "len"),.var .local (ofString "expand_by")]) (memoryExtensionAt 4):=rfl
theorem source_memory_extension_4 : memoryExtensionAt 4=.seq (.ite (.cmp .lower (.var .local (ofString "cap")) (.var .local (ofString "nlen"))) (memoryExtensionGrowthAt 0) .skip) (memoryExtensionAt 5):=rfl
theorem source_memory_extension_5 : memoryExtensionAt 5=.seq (.call (some (none,none)) (ofString "memzero") [.op .add [.load .one (fundingAddress 24),.var .local (ofString "len")],.var .local (ofString "expand_by")]) (memoryExtensionAt 6):=rfl
theorem source_memory_extension_6 : memoryExtensionAt 6=.seq (.store (fundingAddress 32) (.var .local (ofString "nlen"))) (memoryExtensionAt 7):=rfl
theorem source_memory_extension_7 : memoryExtensionAt 7=.return (.const 0):=rfl

theorem source_memory_extension_growth_0 : memoryExtensionGrowthAt 0=.dec (ofString "ncap") .one (.panop .mul [.var .local (ofString "cap"),.const 2]) (memoryExtensionGrowthAt 1):=rfl
theorem source_memory_extension_growth_1 : memoryExtensionGrowthAt 1=.seq (.ite (.cmp .lower (.var .local (ofString "ncap")) (.var .local (ofString "nlen"))) (.assign .local (ofString "ncap") (.op .add [.var .local (ofString "nlen"),.const 1024])) .skip) (memoryExtensionGrowthAt 2):=rfl
theorem source_memory_extension_growth_2 : memoryExtensionGrowthAt 2=.seq (.call (some (none,none)) (ofString "frame_mem_alloc") [.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]) (memoryExtensionGrowthAt 3):=rfl
theorem source_memory_extension_growth_3 : memoryExtensionGrowthAt 3=.seq (.call (some (none,none)) (ofString "memzero") [.op .add [.load .one (fundingAddress 24),.var .local (ofString "cap")],.op .sub [.var .local (ofString "ncap"),.var .local (ofString "cap")]]) (memoryExtensionGrowthAt 4):=rfl
theorem source_memory_extension_growth_4 : memoryExtensionGrowthAt 4=.store (fundingAddress 40) (.var .local (ofString "ncap")):=rfl
#print axioms source_memory_extension_4
#print axioms source_memory_extension_growth_1
end InitECandidate.Runtime
