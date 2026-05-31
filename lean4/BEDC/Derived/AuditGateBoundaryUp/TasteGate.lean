import BEDC.Derived.AuditGateBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.AuditGateBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem AuditGateBoundaryVisibleVerdictExhaustion [AskSetup] [PackageSetup]
    {sourceScan dependencyReport markerResolution originLedger transport route provenance gap
      nameCert verdict : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    AuditGateBoundaryCarrier sourceScan dependencyReport markerResolution originLedger transport
        route provenance gap nameCert bundle pkg ->
      Cont nameCert route verdict ->
        PkgSig bundle verdict pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row verdict ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row sourceScan ∨ hsame row dependencyReport ∨
                  hsame row markerResolution ∨ hsame row originLedger ∨
                    hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                      hsame row gap ∨ hsame row nameCert ∨ hsame row verdict)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle verdict pkg ∧ PkgSig bundle nameCert pkg)
              hsame ∧
            UnaryHistory verdict ∧ PkgSig bundle nameCert pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier nameRouteVerdict verdictPkg
  obtain ⟨_sourceUnary, _dependencyUnary, _markerUnary, _originUnary, _transportUnary,
    routeUnary, _provenanceUnary, _gapUnary, nameUnary, _dependencyGap, _nameGap,
    _sourceDependencyMarker, _markerOriginTransport, _transportRouteProvenance,
    _provenanceGapName, _provenancePkg, namePkg⟩ := carrier
  have verdictUnary : UnaryHistory verdict :=
    unary_cont_closed nameUnary routeUnary nameRouteVerdict
  have sourceVerdict :
      (fun row : BHist => hsame row verdict ∧ UnaryHistory row) verdict := by
    exact ⟨hsame_refl verdict, verdictUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row verdict ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row sourceScan ∨ hsame row dependencyReport ∨
              hsame row markerResolution ∨ hsame row originLedger ∨
                hsame row transport ∨ hsame row route ∨ hsame row provenance ∨
                  hsame row gap ∨ hsame row nameCert ∨ hsame row verdict)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle verdict pkg ∧ PkgSig bundle nameCert pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro verdict sourceVerdict
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
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, verdictPkg, namePkg⟩
  }
  exact ⟨cert, verdictUnary, namePkg⟩

end BEDC.Derived.AuditGateBoundaryUp
