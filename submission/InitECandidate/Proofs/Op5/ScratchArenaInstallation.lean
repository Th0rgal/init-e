import InitECandidate.Proofs.Op5.CompileSemanticsArena
import InitECandidate.Proofs.Op5.ArenaLayouts

namespace InitE.Op5
open Flapjack Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.BackendProof Flapjack.Basis.Pure.MlString
open Flapjack.Pancake.PanLang Flapjack.SemanticsPropsHOL
open Flapjack.Pancake.Proofs.PanToTarget

/-- Re-export of the end-to-end two-region scratch arena compiler semantics theorem. -/
theorem scratchArenaCompileSemantics {width : Nat} [NeZero width] {S Q σ : Type}
    (c : Backend.Config) (mc : MachineConfig width S Q) (pan_code : List (DeclHOL width))
    (bytes : List (BitVec 8)) (bitmaps : List (BitVec width)) (c' : Backend.Config)
    (stack_max : Option Nat) (s : PanSemStateFiniteExact width σ) (ffi : HolFfiState σ)
    (ms : S) (globals_size heap_len : Nat) (adj_ptr2 adj_ptr4 : BitVec width)
    (cbspace data_sp : Nat) (start : MlS)
    (byteArena : BitVec width → Bool) (arena : BitVec width → Prop) :
    compileSemanticsWithArenaStatement c mc pan_code bytes bitmaps c' stack_max s ffi ms
      globals_size heap_len adj_ptr2 adj_ptr4 cbspace data_sp start byteArena arena :=
  compileSemanticsWithArena c mc pan_code bytes bitmaps c' stack_max s ffi ms
    globals_size heap_len adj_ptr2 adj_ptr4 cbspace data_sp start byteArena arena

end InitE.Op5
