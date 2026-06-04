import BEDC.Derived.EquicontinuityUp

namespace BEDC.Derived.EquicontinuityUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem EquicontinuityRootObligationSourceFamily [AskSetup] [PackageSetup]
    {K F eps rho M T R P N radiusRead handoffRead sourceFamilyRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    EquicontinuityCarrier K F eps rho M T R P N radiusRead handoffRead bundle pkg →
      Cont K F sourceFamilyRead →
        Cont sourceFamilyRead rho handoffRead →
          PkgSig bundle sourceFamilyRead pkg →
            SemanticNameCert
                (fun row : BHist => hsame row sourceFamilyRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row K ∨ hsame row F ∨ hsame row rho ∨
                    hsame row sourceFamilyRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont K F sourceFamilyRead ∧
                    Cont sourceFamilyRead rho handoffRead ∧
                      PkgSig bundle sourceFamilyRead pkg)
                hsame ∧ UnaryHistory sourceFamilyRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: EquicontinuityCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceFamilyRoute sourceHandoff sourceFamilyPkg
  obtain ⟨unaryK, unaryF, unaryRho, _unaryR, _unaryN, _radiusRoute,
    _radiusHandoff, _pkgP, _pkgN⟩ := carrier
  have sourceFamilyUnary : UnaryHistory sourceFamilyRead :=
    unary_cont_closed unaryK unaryF sourceFamilyRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed sourceFamilyUnary unaryRho sourceHandoff
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sourceFamilyRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row F ∨ hsame row rho ∨ hsame row sourceFamilyRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont K F sourceFamilyRead ∧
              Cont sourceFamilyRead rho handoffRead ∧ PkgSig bundle sourceFamilyRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sourceFamilyRead ⟨hsame_refl sourceFamilyRead, sourceFamilyUnary⟩
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
      exact ⟨source.right, sourceFamilyRoute, sourceHandoff, sourceFamilyPkg⟩
  }
  exact ⟨cert, sourceFamilyUnary, handoffUnary⟩

end BEDC.Derived.EquicontinuityUp
