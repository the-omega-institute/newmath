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

def OptimalTransportFiniteCouplingPacket [AskSetup] [PackageSetup]
    (sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective feasible dual provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory sourceSupport ∧ UnaryHistory targetSupport ∧ UnaryHistory sourceMass ∧
    UnaryHistory targetMass ∧ UnaryHistory cost ∧ UnaryHistory coupling ∧
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧ UnaryHistory objective ∧
        UnaryHistory feasible ∧ UnaryHistory dual ∧ UnaryHistory provenance ∧
          Cont coupling sourceMass sourceMarginal ∧
            Cont coupling targetMass targetMarginal ∧ Cont cost coupling objective ∧
              Cont sourceMarginal targetMarginal feasible ∧ Cont objective feasible dual ∧
                Cont dual provenance provenance ∧ PkgSig bundle provenance pkg

theorem OptimalTransportFiniteCouplingPacket_marginal_ledger [AskSetup] [PackageSetup]
    {sourceSupport targetSupport sourceMass targetMass cost coupling sourceMarginal
      targetMarginal objective feasible dual provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    OptimalTransportFiniteCouplingPacket sourceSupport targetSupport sourceMass targetMass cost
        coupling sourceMarginal targetMarginal objective feasible dual provenance bundle pkg ->
      UnaryHistory sourceMarginal ∧ UnaryHistory targetMarginal ∧
        hsame sourceMarginal (append coupling sourceMass) ∧
          hsame targetMarginal (append coupling targetMass) ∧ PkgSig bundle provenance pkg := by
  intro packet
  obtain ⟨_sourceSupportUnary, _targetSupportUnary, _sourceMassUnary, _targetMassUnary,
    _costUnary, _couplingUnary, sourceMarginalUnary, targetMarginalUnary, _objectiveUnary,
    _feasibleUnary, _dualUnary, _provenanceUnary, sourceMarginalRow, targetMarginalRow,
    _objectiveRow, _feasibleRow, _dualRow, _provenanceRow, pkgRow⟩ := packet
  exact ⟨sourceMarginalUnary, targetMarginalUnary, sourceMarginalRow, targetMarginalRow, pkgRow⟩

end BEDC.Derived.OptimalTransportUp
