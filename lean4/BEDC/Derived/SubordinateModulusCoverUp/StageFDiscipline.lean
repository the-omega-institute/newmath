import BEDC.Derived.SubordinateModulusCoverUp.TasteGate

namespace BEDC.Derived.SubordinateModulusCoverUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.Meta.TasteGate

theorem SubordinateModulusCoverTasteGate_stageF_discipline [AskSetup] [PackageSetup]
    {E bundleSpine centers radii precision pointwise coverage comparisons transport route
      provenance name handoff : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SubordinateModulusCoverCarrier E bundleSpine centers radii precision pointwise coverage
        comparisons transport route provenance name bundle pkg →
      Cont bundleSpine centers handoff →
        PkgSig bundle handoff pkg →
          Nonempty (BHistCarrier SubordinateModulusCoverUp) ∧
            Nonempty (FieldFaithful SubordinateModulusCoverUp) ∧
              FieldFaithful.fields
                  (SubordinateModulusCoverUp.mk E bundleSpine centers radii precision
                    pointwise coverage comparisons transport route provenance name) =
                [E, bundleSpine, centers, radii, precision, pointwise, coverage, comparisons,
                  transport, route, provenance, name] ∧
                SemanticNameCert
                  (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
                  (fun row : BHist =>
                    hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
                      hsame row precision ∨ hsame row coverage)
                  (fun row : BHist =>
                    hsame row handoff ∧ Cont bundleSpine centers handoff ∧
                      PkgSig bundle handoff pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist BHistCarrier FieldFaithful Cont ProbeBundle PkgSig hsame
  intro carrier handoffRoute handoffPkg
  have fields_eq :
      FieldFaithful.fields
          (SubordinateModulusCoverUp.mk E bundleSpine centers radii precision pointwise coverage
            comparisons transport route provenance name) =
        [E, bundleSpine, centers, radii, precision, pointwise, coverage, comparisons,
          transport, route, provenance, name] := by
    rfl
  have sourceHandoff :
      (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg) handoff := by
    exact ⟨hsame_refl handoff, handoffPkg⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoff ∧ PkgSig bundle handoff pkg)
          (fun row : BHist =>
            hsame row bundleSpine ∨ hsame row centers ∨ hsame row radii ∨
              hsame row precision ∨ hsame row coverage)
          (fun row : BHist =>
            hsame row handoff ∧ Cont bundleSpine centers handoff ∧
              PkgSig bundle handoff pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoff sourceHandoff
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
      obtain ⟨_eUnary, _bundleUnary, _centersUnary, _radiiUnary, _precisionUnary,
        _pointwiseUnary, _coverageUnary, _comparisonsUnary, _transportUnary, _routeUnary,
        _provenanceUnary, _nameUnary, coverageRoute, _comparisonRoute, _provenancePkg,
        _namePkg⟩ := carrier
      have handoffCoverage : hsame handoff coverage :=
        hsame_trans handoffRoute (hsame_symm coverageRoute)
      exact Or.inr <| Or.inr <| Or.inr <| Or.inr <|
        hsame_trans source.left handoffCoverage
    ledger_sound := by
      intro _row source
      exact ⟨source.left, handoffRoute, source.right⟩
  }
  exact
    ⟨⟨subordinateModulusCoverBHistCarrier⟩,
      ⟨subordinateModulusCoverFieldFaithful⟩,
      fields_eq,
      cert⟩

end BEDC.Derived.SubordinateModulusCoverUp
