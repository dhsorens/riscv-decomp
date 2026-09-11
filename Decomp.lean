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

import Decomp.Stepper
import Decomp.Triple
import Decomp.Tailrec
import Decomp.Loop
import Decomp.Certificate
import Decomp.Leaf.Core
import Decomp.Leaf.Mem
import Decomp.Leaf.Sp1Step
import Decomp.Leaf.Sp1Text
import Decomp.Leaf.Sp1Mem
import Decomp.Region.Bytes
import Decomp.Region.Wide
import Decomp.Region.Sp1
import Decomp.Sp1.Syscalls
import Decomp.Sp1.HintRead
import Decomp.Reject
import Decomp.Examples.Sp1Ecall
import Decomp.Examples.Countdown
import Decomp.Examples.CountdownMachine
import Decomp.Examples.FindIndex
import Decomp.Examples.FindIndexMachine
