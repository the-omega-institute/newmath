import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.KKTUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def KKTPrimalDualCarrier [AskSetup] [PackageSetup]
    (primal dual residual stationarity feasibility slackness ledger endpoint : BHist)
    (probeBundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
    UnaryHistory stationarity ∧ UnaryHistory feasibility ∧ UnaryHistory slackness ∧
      UnaryHistory ledger ∧ UnaryHistory endpoint ∧ Cont primal residual stationarity ∧
        Cont residual dual slackness ∧ Cont slackness feasibility ledger ∧
          Cont ledger stationarity endpoint ∧ PkgSig probeBundle endpoint pkg

theorem KKTPrimalDualCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasibility slackness ledger endpoint : BHist}
    {probeBundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualCarrier primal dual residual stationarity feasibility slackness ledger endpoint
        probeBundle pkg ->
      SemanticNameCert
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasibility slackness ledger
            endpoint probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasibility slackness ledger
            endpoint probeBundle pkg ∧ hsame row endpoint)
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasibility slackness ledger
            endpoint probeBundle pkg ∧ hsame row endpoint)
        hsame := by
  intro carrier
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro endpoint (And.intro carrier (hsame_refl endpoint))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' same source
        exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.KKTUp
