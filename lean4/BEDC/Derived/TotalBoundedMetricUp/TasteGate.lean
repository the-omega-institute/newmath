import BEDC.Derived.TotallyBoundedMetricUp.TasteGate

namespace BEDC.Derived.TotalBoundedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem TotalBoundedMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {M R E D S Q H C P N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.TotallyBoundedMetricUp.TasteGate.TotallyBoundedMetricCarrier
        M R E D S Q H C P N bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              BEDC.Derived.TotallyBoundedMetricUp.TasteGate.TotallyBoundedMetricCarrier
                M R E D S Q H C P N bundle pkg)
          (fun row : BHist =>
            hsame row N ∧ Cont M R D ∧ Cont D S Q ∧ Cont H C P)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame ∧
        UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory D ∧
          UnaryHistory S ∧ UnaryHistory Q ∧ Cont M R D ∧ Cont D S Q ∧
            Cont H C P ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro carrier
  have carrierSource :
      BEDC.Derived.TotallyBoundedMetricUp.TasteGate.TotallyBoundedMetricCarrier
        M R E D S Q H C P N bundle pkg := carrier
  obtain ⟨MUnary, RUnary, EUnary, DUnary, SUnary, QUnary, _HUnary, _CUnary,
    _PUnary, _NUnary, metricToleranceRoute, windowReadbackRoute, transportReplayRoute,
    provenancePkg, nameCertPkg⟩ := carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row N ∧
              BEDC.Derived.TotallyBoundedMetricUp.TasteGate.TotallyBoundedMetricCarrier
                M R E D S Q H C P N bundle pkg)
          (fun row : BHist =>
            hsame row N ∧ Cont M R D ∧ Cont D S Q ∧ Cont H C P)
          (fun row : BHist => hsame row N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro N
          ⟨hsame_refl N, carrierSource⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
          exact ⟨hsame_trans (hsame_symm sameRows) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact ⟨source.left, metricToleranceRoute, windowReadbackRoute, transportReplayRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, nameCertPkg⟩
    }
  exact
    ⟨cert, MUnary, RUnary, EUnary, DUnary, SUnary, QUnary, metricToleranceRoute,
      windowReadbackRoute, transportReplayRoute, provenancePkg, nameCertPkg⟩

end BEDC.Derived.TotalBoundedMetricUp
