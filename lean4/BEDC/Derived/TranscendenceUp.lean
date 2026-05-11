import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.TranscendenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TranscendenceCarrierPacket [AskSetup] [PackageSetup]
    (fieldExtSource family coeffLedger tests transports readbacks endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory fieldExtSource ∧ UnaryHistory family ∧ UnaryHistory coeffLedger ∧
    UnaryHistory tests ∧ UnaryHistory transports ∧ UnaryHistory readbacks ∧
      Cont fieldExtSource family tests ∧ Cont coeffLedger tests readbacks ∧
        Cont transports readbacks endpoint ∧ PkgSig bundle endpoint pkg

end BEDC.Derived.TranscendenceUp
