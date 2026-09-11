/-
  Decomp.Upstream

  Everything this library takes from `riscv-zkvm`, re-exported once.

  `riscv-zkvm`'s two aggregators, `RiscvZkvm.Rv64` and `RiscvZkvm.Rv64.Logic`,
  are legacy (non-`module`) files, and a `module` cannot import a legacy file.
  Their *contents* are modules almost without exception, so this file imports
  those directly and stands in for the two aggregators. It is the single
  *public-import* hub: every other file reaches upstream's names through
  `public import Decomp.Upstream`. The one kind of exception is a private
  `meta import` of a specific upstream module, needed where a `#guard` *runs*
  an upstream definition -- currently `Sp1/HintRead.lean` (three modules) and
  `Extract/CFG.lean` (two); those import code, not names, and re-export
  nothing.

  Deliberately omitted, because they are legacy files and nothing here uses
  them: `RiscvZkvm.Rv64.Logic.CPSCall`, `RiscvZkvm.Rv64.Logic.MemSat`, `RiscvZkvm.Rv64.Logic.CodeReqExtents`, `RiscvZkvm.Rv64.Logic.WP.Examples`, `RiscvZkvm.Rv64.Logic.Tactics.WP`. If one is needed, the upstream ask is to put `module` at the top
  of it; the downstream workaround is a legacy file of one's own.

  Regenerate the list from the two aggregators when the pin moves.
-/

module

public import RiscvZkvm.Rv64.Execution
public import RiscvZkvm.Rv64.StepOn
public import RiscvZkvm.Rv64.Program
public import RiscvZkvm.Rv64.Bytes
public import RiscvZkvm.Rv64.Logic.Support
public import RiscvZkvm.Rv64.Logic.SepLogic
public import RiscvZkvm.Rv64.Logic.Sp1Mem
public import RiscvZkvm.Rv64.Logic.CPSSpec
public import RiscvZkvm.Rv64.Logic.GenericSpecs
public import RiscvZkvm.Rv64.Logic.InstructionSpecs
public import RiscvZkvm.Rv64.Logic.SyscallSpecs
public import RiscvZkvm.Rv64.Logic.HintSpecs
public import RiscvZkvm.Rv64.Logic.MemRegion
public import RiscvZkvm.Rv64.Logic.MemRegionWrite
public import RiscvZkvm.Rv64.Logic.MemRegionWriteWide
public import RiscvZkvm.Rv64.Logic.MemRegionStore
public import RiscvZkvm.Rv64.Logic.MemRegionStoreWide
public import RiscvZkvm.Rv64.Logic.ByteOps
public import RiscvZkvm.Rv64.Logic.HalfwordOps
public import RiscvZkvm.Rv64.Logic.WordOps
public import RiscvZkvm.Rv64.Logic.ControlFlow
public import RiscvZkvm.Rv64.Logic.LaResolve
public import RiscvZkvm.Rv64.Logic.BranchRelaxation
public import RiscvZkvm.Rv64.Logic.RegOps
public import RiscvZkvm.Rv64.Logic.RegOpsAttr
public import RiscvZkvm.Rv64.Logic.AddrNorm
public import RiscvZkvm.Rv64.Logic.AddrNormAttr
public import RiscvZkvm.Rv64.Logic.ByteAlg
public import RiscvZkvm.Rv64.Logic.ByteAlgAttr
public import RiscvZkvm.Rv64.Logic.BitAux
public import RiscvZkvm.Rv64.Logic.RemuNat
public import RiscvZkvm.Rv64.Logic.SignExtendSimproc
public import RiscvZkvm.Rv64.Logic.WP.Core
public import RiscvZkvm.Rv64.Logic.WP.CFG
public import RiscvZkvm.Rv64.Logic.WP.Call
public import RiscvZkvm.Rv64.Logic.WP.Loop
public import RiscvZkvm.Rv64.Logic.WP.GeneratedCFG
public import RiscvZkvm.Rv64.Logic.Tactics.SeqFrame
public import RiscvZkvm.Rv64.Logic.Tactics.RunBlock
public import RiscvZkvm.Rv64.Logic.Tactics.SpecDb
public import RiscvZkvm.Rv64.Logic.Tactics.SymStep
public import RiscvZkvm.Rv64.Logic.Tactics.WPAttr
public import RiscvZkvm.Rv64.Logic.Tactics.ExtractPure
public import RiscvZkvm.Rv64.Logic.Tactics.DropPure
public import RiscvZkvm.Rv64.Logic.Tactics.XSimp
public import RiscvZkvm.Rv64.Logic.Tactics.XPerm
public import RiscvZkvm.Rv64.Logic.Tactics.XPermPartial
public import RiscvZkvm.Rv64.Logic.Tactics.XPermPure
public import RiscvZkvm.Rv64.Logic.Tactics.XPermChunked
public import RiscvZkvm.Rv64.Logic.Tactics.XPermCert
public import RiscvZkvm.Rv64.Logic.Tactics.XCancel
public import RiscvZkvm.Rv64.Logic.Tactics.XCancelStruct
public import RiscvZkvm.Rv64.Logic.Tactics.PerfTrace
