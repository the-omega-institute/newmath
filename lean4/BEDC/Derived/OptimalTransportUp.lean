import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptimalTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OptimalTransportFiniteCoupling [AskSetup] [PackageSetup]
    (sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceSupport ∧ UnaryHistory targetSupport ∧ UnaryHistory sourceMass ∧
    UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧
        UnaryHistory objective ∧ UnaryHistory provenance ∧
          Cont sourceSupport coupling sourceMarginal ∧
            Cont targetSupport coupling targetMarginal ∧
              Cont cost coupling objective ∧ Cont objective provenance objective ∧
                PkgSig bundle objective pkg

theorem OptimalTransportFiniteCoupling_marginal_ledger [AskSetup] [PackageSetup]
    {sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCoupling sourceSupport targetSupport sourceMass targetMass cost
        coupling sourceMarginal targetMarginal objective provenance bundle pkg ->
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧
        Cont sourceSupport coupling sourceMarginal ∧
          Cont targetSupport coupling targetMarginal ∧
            hsame sourceMarginal (append sourceSupport coupling) ∧
              hsame targetMarginal (append targetSupport coupling) ∧
                PkgSig bundle objective pkg := by
  intro carrier
  obtain ⟨_sourceSupportUnary, _targetSupportUnary, _sourceMassUnary, _targetMassUnary,
    _costUnary, _couplingUnary, sourceMarginalUnary, targetMarginalUnary, _objectiveUnary,
    _provenanceUnary, sourceMarginalRow, targetMarginalRow, _objectiveRow,
    _provenanceRow, pkgRow⟩ := carrier
  exact
    ⟨sourceMarginalUnary, targetMarginalUnary, sourceMarginalRow, targetMarginalRow,
      sourceMarginalRow, targetMarginalRow, pkgRow⟩

end BEDC.Derived.OptimalTransportUp
