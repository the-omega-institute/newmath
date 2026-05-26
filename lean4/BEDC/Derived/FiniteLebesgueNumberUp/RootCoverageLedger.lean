import BEDC.Derived.FiniteLebesgueNumberUp.Core

namespace BEDC.Derived.FiniteLebesgueNumberUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def FiniteLebesgueNumberRootCoverageLedger [AskSetup] [PackageSetup]
    (cover mesh radius stream regular real selector transport replay provenance
      nameRow : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  FiniteLebesgueNumberCarrier cover stream radius mesh transport replay provenance
      nameRow bundle pkg ∧
    UnaryHistory real ∧ Cont cover mesh radius ∧ Cont radius stream regular ∧
      Cont regular real selector ∧ PkgSig bundle selector pkg

theorem FiniteLebesgueNumberRootCoverageLedger_certificate [AskSetup] [PackageSetup]
    {cover mesh radius stream regular real selector transport replay provenance
      nameRow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteLebesgueNumberRootCoverageLedger cover mesh radius stream regular real selector
        transport replay provenance nameRow bundle pkg →
      UnaryHistory cover ∧ UnaryHistory mesh ∧ UnaryHistory radius ∧
        UnaryHistory stream ∧ UnaryHistory regular ∧ UnaryHistory real ∧
          UnaryHistory selector ∧ Cont cover mesh radius ∧
            Cont radius stream regular ∧ Cont regular real selector ∧
              PkgSig bundle selector pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory
  intro ledger
  obtain ⟨carrier, realUnary, coverMeshRadius, radiusStreamRegular, regularRealSelector,
    selectorPkg⟩ := ledger
  obtain ⟨coverUnary, streamUnary, radiusUnary, meshUnary, _transportUnary, _replayUnary,
    _provenanceUnary, _nameRowUnary, _coverStreamRadius, _radiusMeshReplay,
    _replayNameProvenance, _provenancePkg⟩ := carrier
  have radiusUnaryFromLedger : UnaryHistory radius :=
    unary_cont_closed coverUnary meshUnary coverMeshRadius
  have regularUnary : UnaryHistory regular :=
    unary_cont_closed radiusUnaryFromLedger streamUnary radiusStreamRegular
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed regularUnary realUnary regularRealSelector
  exact
    ⟨coverUnary, meshUnary, radiusUnaryFromLedger, streamUnary, regularUnary, realUnary,
      selectorUnary, coverMeshRadius, radiusStreamRegular, regularRealSelector,
      selectorPkg⟩

end BEDC.Derived.FiniteLebesgueNumberUp
