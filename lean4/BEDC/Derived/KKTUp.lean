import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KKTUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KKTFinitePacket [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasibility slackness comparison contLedger pkgRow
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧ UnaryHistory comparison ∧
    Cont primal dual stationarity ∧ Cont stationarity residual feasibility ∧
      Cont residual dual slackness ∧ Cont comparison slackness contLedger ∧
        Cont contLedger pkgRow endpoint ∧ PkgSig bundle endpoint pkg

theorem KKTFinitePacket_complementarity_ledger_exactness [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness comparison contLedger pkgRow endpoint :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTFinitePacket primal dual residual stationarity feasibility slackness comparison contLedger
        pkgRow endpoint bundle pkg ->
      UnaryHistory slackness ∧ hsame slackness (append residual dual) ∧
        UnaryHistory contLedger ∧ hsame contLedger (append comparison slackness) ∧
          Cont residual dual slackness ∧ Cont comparison slackness contLedger ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have slacknessUnary : UnaryHistory slackness :=
    unary_cont_closed packet.right.right.left packet.right.left
      packet.right.right.right.right.right.right.left
  have contLedgerUnary : UnaryHistory contLedger :=
    unary_cont_closed packet.right.right.right.left slacknessUnary
      packet.right.right.right.right.right.right.right.left
  exact And.intro slacknessUnary
    (And.intro packet.right.right.right.right.right.right.left
      (And.intro contLedgerUnary
        (And.intro packet.right.right.right.right.right.right.right.left
          (And.intro packet.right.right.right.right.right.right.left
            (And.intro packet.right.right.right.right.right.right.right.left
              packet.right.right.right.right.right.right.right.right.right)))))

end BEDC.Derived.KKTUp
