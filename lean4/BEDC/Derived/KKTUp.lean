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

def KKTPrimalDualPacket [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasibility slackness comparison stationarityReadback
      ledgerReadback dependencyPkg namecertRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
    UnaryHistory feasibility ∧ UnaryHistory slackness ∧ UnaryHistory comparison ∧
      hsame stationarity (append primal residual) ∧ Cont primal residual stationarity ∧
        Cont stationarity feasibility stationarityReadback ∧
          Cont comparison slackness ledgerReadback ∧ PkgSig bundle dependencyPkg pkg ∧
            hsame namecertRow ledgerReadback

theorem KKTPrimalDualPacket_row_obligations [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness comparison stationarityReadback
      ledgerReadback dependencyPkg namecertRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualPacket primal dual residual stationarity feasibility slackness comparison
        stationarityReadback ledgerReadback dependencyPkg namecertRow bundle pkg ->
      UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
        UnaryHistory feasibility ∧ UnaryHistory slackness ∧ UnaryHistory comparison ∧
          UnaryHistory stationarity ∧ UnaryHistory stationarityReadback ∧
            UnaryHistory ledgerReadback ∧ hsame stationarity (append primal residual) ∧
              hsame ledgerReadback (append comparison slackness) ∧
                Cont primal residual stationarity ∧
                  Cont stationarity feasibility stationarityReadback ∧
                    Cont comparison slackness ledgerReadback ∧
                      PkgSig bundle dependencyPkg pkg ∧ hsame namecertRow ledgerReadback := by
  intro packet
  have primalUnary : UnaryHistory primal := packet.left
  have dualUnary : UnaryHistory dual := packet.right.left
  have residualUnary : UnaryHistory residual := packet.right.right.left
  have feasibilityUnary : UnaryHistory feasibility := packet.right.right.right.left
  have slacknessUnary : UnaryHistory slackness := packet.right.right.right.right.left
  have comparisonUnary : UnaryHistory comparison := packet.right.right.right.right.right.left
  have stationaritySame : hsame stationarity (append primal residual) :=
    packet.right.right.right.right.right.right.left
  have stationarityCont : Cont primal residual stationarity :=
    packet.right.right.right.right.right.right.right.left
  have stationarityReadbackCont : Cont stationarity feasibility stationarityReadback :=
    packet.right.right.right.right.right.right.right.right.left
  have ledgerReadbackCont : Cont comparison slackness ledgerReadback :=
    packet.right.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle dependencyPkg pkg :=
    packet.right.right.right.right.right.right.right.right.right.right.left
  have namecertSame : hsame namecertRow ledgerReadback :=
    packet.right.right.right.right.right.right.right.right.right.right.right
  have stationarityUnary : UnaryHistory stationarity :=
    unary_cont_closed primalUnary residualUnary stationarityCont
  have stationarityReadbackUnary : UnaryHistory stationarityReadback :=
    unary_cont_closed stationarityUnary feasibilityUnary stationarityReadbackCont
  have ledgerReadbackUnary : UnaryHistory ledgerReadback :=
    unary_cont_closed comparisonUnary slacknessUnary ledgerReadbackCont
  exact
    ⟨primalUnary, dualUnary, residualUnary, feasibilityUnary, slacknessUnary,
      comparisonUnary, stationarityUnary, stationarityReadbackUnary, ledgerReadbackUnary,
      stationaritySame, ledgerReadbackCont, stationarityCont, stationarityReadbackCont,
      ledgerReadbackCont, pkgSig, namecertSame⟩

end BEDC.Derived.KKTUp
