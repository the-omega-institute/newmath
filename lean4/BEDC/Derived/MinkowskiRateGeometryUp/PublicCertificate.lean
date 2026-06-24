import BEDC.Derived.MinkowskiRateGeometryUp.Carrier

namespace BEDC.Derived.MinkowskiRateGeometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MinkowskiRateGeometryPublicCertificate [AskSetup] [PackageSetup]
    {G X R L D H C P N geometryRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MinkowskiRateGeometryCarrier G X R L D H C P N bundle pkg →
      Cont L D geometryRead →
        PkgSig bundle geometryRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row geometryRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row G ∨ hsame row X ∨ hsame row R ∨ hsame row L ∨
                  hsame row D ∨ hsame row geometryRead)
              (fun row : BHist =>
                hsame row geometryRead ∧ Cont L D geometryRead ∧
                  PkgSig bundle geometryRead pkg)
              hsame ∧ UnaryHistory geometryRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier frameDistanceGeometry geometryPkg
  obtain ⟨_configUnary, _causalUnary, _rateUnary, frameUnary, distanceUnary,
    _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary, _configCausalRate,
    _rateFrameDistance, _distanceTransportReplay, _distancePkg, _provenancePkg,
    _localNamePkg⟩ := carrier
  have geometryUnary : UnaryHistory geometryRead :=
    unary_cont_closed frameUnary distanceUnary frameDistanceGeometry
  have sourceGeometry :
      (fun row : BHist => hsame row geometryRead ∧ UnaryHistory row) geometryRead := by
    exact ⟨hsame_refl geometryRead, geometryUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row geometryRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row X ∨ hsame row R ∨ hsame row L ∨
              hsame row D ∨ hsame row geometryRead)
          (fun row : BHist =>
            hsame row geometryRead ∧ Cont L D geometryRead ∧
              PkgSig bundle geometryRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro geometryRead sourceGeometry
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left))))
    ledger_sound := by
      intro _row sourceRow
      exact ⟨sourceRow.left, frameDistanceGeometry, geometryPkg⟩
  }
  exact ⟨cert, geometryUnary⟩

end BEDC.Derived.MinkowskiRateGeometryUp
