import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.OptimalTransportUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def OptimalTransportFiniteCouplingCarrier [AskSetup] [PackageSetup]
    (source target sourceMass targetMass cost coupling sourceMarginal targetMarginal objective
      feasible dual provenance : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory target ∧ UnaryHistory sourceMass ∧
    UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      Cont source coupling sourceMarginal ∧ Cont target coupling targetMarginal ∧
        Cont cost coupling objective ∧ Cont objective feasible dual ∧
          Cont dual sourceMarginal provenance ∧ PkgSig bundle provenance pkg

theorem OptimalTransportFiniteCouplingCarrier_marginal_ledger [AskSetup] [PackageSetup]
    {source target sourceMass targetMass cost coupling sourceMarginal targetMarginal objective
      feasible dual provenance : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingCarrier source target sourceMass targetMass cost coupling
        sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧
        hsame sourceMarginal (append source coupling) ∧
          hsame targetMarginal (append target coupling) ∧ PkgSig bundle provenance pkg := by
  intro carrier
  obtain ⟨sourceUnary, targetUnary, _sourceMassUnary, _targetMassUnary, _costUnary,
    couplingUnary, sourceMarginalRow, targetMarginalRow, _objectiveRow, _dualRow,
    _provenanceRow, pkgRow⟩ := carrier
  have sourceMarginalUnary : UnaryHistory sourceMarginal :=
    unary_cont_closed sourceUnary couplingUnary sourceMarginalRow
  have targetMarginalUnary : UnaryHistory targetMarginal :=
    unary_cont_closed targetUnary couplingUnary targetMarginalRow
  exact
    ⟨sourceMarginalUnary, targetMarginalUnary, sourceMarginalRow, targetMarginalRow, pkgRow⟩

end BEDC.Derived.OptimalTransportUp
