import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Package
import BEDC.Derived.MeasureUp

namespace BEDC.Derived.MeasureUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package

def MeasureComplementDifferenceRow [AskSetup] [PackageSetup]
    (base event diff union endpoint provenance : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  MeasureZeroBHistCarrier base ∧ MeasureZeroBHistClassifier event BHist.Empty ∧
    MeasureZeroBHistClassifier diff BHist.Empty ∧ Cont event diff union ∧
      Cont union provenance endpoint ∧ hsame endpoint (append union provenance) ∧
        PkgSig bundle endpoint pkg

theorem MeasureComplementDifferenceRow_zero_coverage [AskSetup] [PackageSetup]
    {base event diff union endpoint provenance : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MeasureComplementDifferenceRow base event diff union endpoint provenance bundle pkg ->
      hsame provenance BHist.Empty ->
        MeasureZeroBHistClassifier union BHist.Empty ∧ MeasureZeroBHistCarrier endpoint ∧
          PkgSig bundle endpoint pkg := by
  intro row provenanceZero
  obtain ⟨_baseCarrier, eventZero, diffZero, unionRow, _endpointRow, endpointSame,
    pkgSig⟩ := row
  have unionZero : MeasureZeroBHistCarrier union :=
    cont_respects_hsame eventZero.left diffZero.left unionRow (cont_left_unit BHist.Empty)
  have unionClassified : MeasureZeroBHistClassifier union BHist.Empty :=
    And.intro unionZero (And.intro (hsame_refl BHist.Empty) unionZero)
  have appendZero : hsame (append union provenance) BHist.Empty := by
    cases unionZero
    cases provenanceZero
    rfl
  have endpointZero : MeasureZeroBHistCarrier endpoint :=
    hsame_trans endpointSame appendZero
  exact ⟨unionClassified, endpointZero, pkgSig⟩

end BEDC.Derived.MeasureUp
