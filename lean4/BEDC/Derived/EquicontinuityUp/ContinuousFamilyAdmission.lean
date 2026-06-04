import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityContinuousFamilyAdmission [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead familyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      Cont K F familyRead ->
        PkgSig bundle familyRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row familyRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row K ∨ hsame row F ∨ hsame row radiusRead ∨ hsame row familyRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont K F familyRead ∧ PkgSig bundle familyRead pkg)
              hsame ∧ UnaryHistory K ∧ UnaryHistory F ∧ UnaryHistory familyRead ∧
            Cont K F familyRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle familyRead pkg := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier familyRoute familyPkg
  obtain ⟨unaryK, unaryF, _unaryRho, _unaryR, _unaryN, _radiusRoute, _handoffRoute,
    pkgP, _pkgN⟩ := carrier
  have familyUnary : UnaryHistory familyRead :=
    unary_cont_closed unaryK unaryF familyRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row familyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row radiusRead ∨ hsame row familyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F familyRead ∧ PkgSig bundle familyRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro familyRead ⟨hsame_refl familyRead, familyUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, familyRoute, familyPkg⟩
  }
  exact ⟨cert, unaryK, unaryF, familyUnary, familyRoute, pkgP, familyPkg⟩

end BEDC.Derived.EquicontinuityUp
