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
    (primal dual residual stationarity feasible slack ledger provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
    UnaryHistory stationarity ∧ UnaryHistory feasible ∧ UnaryHistory slack ∧
      UnaryHistory ledger ∧ UnaryHistory provenance ∧ Cont primal residual stationarity ∧
        Cont dual slack ledger ∧ Cont stationarity feasible provenance ∧
          PkgSig bundle provenance pkg

theorem KKTPrimalDualCarrier_primal_dual_row_obligations [AskSetup] [PackageSetup]
    {primal dual residual stationarity feasible slack ledger provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger provenance
        bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          (fun row : BHist =>
            KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
              provenance bundle pkg ∧ hsame row provenance)
          hsame ∧
        UnaryHistory primal ∧ UnaryHistory dual ∧ UnaryHistory residual ∧
          UnaryHistory stationarity ∧ UnaryHistory feasible ∧ UnaryHistory slack ∧
            UnaryHistory ledger ∧ UnaryHistory provenance ∧
              Cont primal residual stationarity ∧ Cont dual slack ledger ∧
                Cont stationarity feasible provenance ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
            provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
            provenance bundle pkg ∧ hsame row provenance)
        (fun row : BHist =>
          KKTPrimalDualCarrier primal dual residual stationarity feasible slack ledger
            provenance bundle pkg ∧ hsame row provenance)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro provenance (And.intro carrier (hsame_refl provenance))
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
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
  exact And.intro cert carrier

end BEDC.Derived.KKTUp
