import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLebesgueNumberObligationCoverageRow [AskSetup] [PackageSetup]
    {cover window radius mesh transport replay provenance nameRow streamRead regularRead
      realRead coverCell : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberCarrier cover window radius mesh transport replay provenance nameRow
        bundle pkg →
      Cont window streamRead regularRead →
        Cont regularRead realRead mesh →
          Cont mesh cover coverCell →
            PkgSig bundle coverCell pkg →
              UnaryHistory cover ∧ UnaryHistory window ∧ UnaryHistory radius ∧
                UnaryHistory mesh ∧ Cont window streamRead regularRead ∧
                  Cont regularRead realRead mesh ∧ Cont mesh cover coverCell ∧
                    PkgSig bundle coverCell pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro carrier windowStreamRegular regularRealMesh meshCoverCell coverCellPkg
  obtain ⟨coverUnary, windowUnary, radiusUnary, meshUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameRowUnary, _coverWindowRadius, _radiusMeshReplay,
    _replayNameProvenance, _provenancePkg⟩ := carrier
  exact
    ⟨coverUnary, windowUnary, radiusUnary, meshUnary, windowStreamRegular,
      regularRealMesh, meshCoverCell, coverCellPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
