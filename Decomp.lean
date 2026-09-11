/-
  Myreen

  Myreen-style decompilation into logic for RISC-V, over an abstract stepper.

  The namespace is `Decomp` because the method is: Magnus Myreen's
  decompilation into logic (UCAM-CL-TR-765), where a machine-code region is
  turned into a tail-recursive function plus a certificate theorem, and every
  proof about the code is a proof about that function. See `README.md` for the
  shape and `ROADMAP.md` for what is not here yet.

  Import order below follows the dependency order, which is also roughly the
  order to read them in: the stepper interface, the judgements, the abstract
  loop, the certificate contract, then the leaves and regions that make real
  instructions usable, then SP1's ABI, then the worked examples.
-/

module

public import Decomp.Upstream
public import Decomp.Stepper
public import Decomp.Triple
public import Decomp.Tailrec
public import Decomp.Loop
public import Decomp.Certificate
public import Decomp.Leaf.Core
public import Decomp.Leaf.Mem
public import Decomp.Leaf.Sp1Step
public import Decomp.Leaf.Sp1Text
public import Decomp.Leaf.Sp1Mem
public import Decomp.Region.Bytes
public import Decomp.Region.Wide
public import Decomp.Region.Sp1
public import Decomp.Sp1.Syscalls
public import Decomp.Sp1.HintRead
public import Decomp.Reject
public import Decomp.Refine
public import Decomp.Extract.CFG
public import Decomp.Extract.Body
public import Decomp.Examples.Sp1Ecall
public import Decomp.Examples.Countdown
public import Decomp.Examples.CountdownMachine
public import Decomp.Examples.FindIndex
public import Decomp.Examples.FindIndexMachine
public import Decomp.Examples.FindIndexRefine
public import Decomp.Examples.CountdownThenFind
