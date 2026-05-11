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

def KKTComplementarityPacket [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasibility slack provenance complementarity endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧ UnaryHistory stationarity ∧
    UnaryHistory feasibility ∧ UnaryHistory slack ∧ UnaryHistory provenance ∧
      Cont residual dual stationarity ∧ Cont stationarity slack complementarity ∧
        Cont complementarity provenance endpoint ∧ PkgSig bundle endpoint pkg

theorem KKTComplementarityPacket_ledger_exactness [AskSetup] [PackageSetup]
    {bundle : ProbeBundle ProbeName} {pkg : Pkg}
    {primal dual residual stationarity feasibility slack provenance complementarity endpoint :
      BHist} :
    KKTComplementarityPacket primal dual residual stationarity feasibility slack provenance
        complementarity endpoint bundle pkg ->
      UnaryHistory residual ∧ UnaryHistory dual ∧ UnaryHistory slack ∧
        UnaryHistory complementarity ∧
          hsame complementarity (append (append residual dual) slack) ∧
            PkgSig bundle endpoint pkg := by
  intro packet
  have dualUnary : UnaryHistory dual :=
    packet.right.left
  have residualUnary : UnaryHistory residual :=
    packet.right.right.left
  have slackUnary : UnaryHistory slack :=
    packet.right.right.right.right.right.left
  have stationarityRow : Cont residual dual stationarity :=
    packet.right.right.right.right.right.right.right.left
  have complementarityRow : Cont stationarity slack complementarity :=
    packet.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle endpoint pkg :=
    packet.right.right.right.right.right.right.right.right.right.right
  have stationarityUnary : UnaryHistory stationarity :=
    unary_cont_closed residualUnary dualUnary stationarityRow
  have complementarityUnary : UnaryHistory complementarity :=
    unary_cont_closed stationarityUnary slackUnary complementarityRow
  have complementarityReadback :
      hsame complementarity (append (append residual dual) slack) :=
    hsame_trans complementarityRow
      (congrArg (fun row : BHist => append row slack) stationarityRow)
  exact And.intro residualUnary
    (And.intro dualUnary
      (And.intro slackUnary
        (And.intro complementarityUnary (And.intro complementarityReadback pkgSig))))

end BEDC.Derived.KKTUp
