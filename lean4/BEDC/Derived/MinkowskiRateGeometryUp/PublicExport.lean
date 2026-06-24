import BEDC.Derived.MinkowskiRateGeometryUp.Carrier

namespace BEDC.Derived.MinkowskiRateGeometryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem MinkowskiRateGeometryPublicExport [AskSetup] [PackageSetup]
    {G X R L D H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    MinkowskiRateGeometryCarrier G X R L D H C P N bundle pkg →
      Cont D N publicRead →
        PkgSig bundle publicRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row G ∨ hsame row X ∨ hsame row R ∨ hsame row L ∨
                  hsame row D ∨ hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont G X R ∧ Cont R L D ∧ Cont D N publicRead ∧
                  PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
              hsame ∧ UnaryHistory publicRead ∧ PkgSig bundle P pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier publicRoute publicPkg
  obtain ⟨_gUnary, _xUnary, _rUnary, _lUnary, distanceUnary, _hUnary, _cUnary,
    provenanceUnary, nameUnary, configCausalRate, rateFrameDistance, _distanceReplay,
    _distancePkg, provenancePkg, _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed distanceUnary nameUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row G ∨ hsame row X ∨ hsame row R ∨ hsame row L ∨
              hsame row D ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont G X R ∧ Cont R L D ∧ Cont D N publicRead ∧
              PkgSig bundle P pkg ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicUnary⟩
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
      exact
        ⟨sourceRow.right, configCausalRate, rateFrameDistance, publicRoute,
          provenancePkg, publicPkg⟩
  }
  exact ⟨cert, publicUnary, provenancePkg⟩

end BEDC.Derived.MinkowskiRateGeometryUp
