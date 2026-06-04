import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityCompactSourceAdmission [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead compactRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg ->
      Cont K F compactRead ->
        PkgSig bundle compactRead pkg ->
          SemanticNameCert
              (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row K ∨ hsame row F ∨ hsame row radiusRead ∨
                hsame row compactRead)
              (fun row : BHist =>
                UnaryHistory row ∧ PkgSig bundle compactRead pkg ∧
                  Cont K F compactRead ∧ PkgSig bundle P pkg)
              hsame ∧ UnaryHistory compactRead ∧ Cont K F compactRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle PkgSig Cont hsame SemanticNameCert UnaryHistory
  intro carrier compactRoute compactPkg
  obtain ⟨unaryK, unaryF, _unaryRho, _unaryR, _unaryN, _radiusRoute, _handoffRoute,
    pkgP, _pkgN⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed unaryK unaryF compactRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row compactRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row radiusRead ∨ hsame row compactRead)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle compactRead pkg ∧ Cont K F compactRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro compactRead ⟨hsame_refl compactRead, compactUnary⟩
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
      exact ⟨source.right, compactPkg, compactRoute, pkgP⟩
  }
  exact ⟨cert, compactUnary, compactRoute⟩

end BEDC.Derived.EquicontinuityUp
