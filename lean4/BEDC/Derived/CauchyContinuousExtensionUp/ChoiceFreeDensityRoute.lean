import BEDC.Derived.CauchyContinuousExtensionUp.RegularTailTransport

namespace BEDC.Derived.CauchyContinuousExtensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionCarrier_choice_free_density_route [AskSetup] [PackageSetup]
    {S W D F U L H C P N densityRead extensionRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyContinuousExtensionCarrier S W D F U L H C P N bundle pkg →
      Cont S D densityRead →
        Cont densityRead F extensionRead →
          Cont extensionRead N named →
            PkgSig bundle named pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row named ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row D ∨ hsame row F ∨ hsame row N ∨
                      hsame row named)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S D densityRead ∧
                      Cont densityRead F extensionRead ∧ Cont extensionRead N named ∧
                        PkgSig bundle named pkg)
                  hsame ∧
                UnaryHistory densityRead ∧ UnaryHistory extensionRead ∧
                  UnaryHistory named := by
  -- BEDC touchpoint anchor: CauchyContinuousExtensionCarrier BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier densityRoute extensionRoute namedRoute namedPkg
  obtain ⟨unaryS, _unaryW, unaryD, unaryF, _unaryU, _unaryL, _unaryH, _unaryC,
    _unaryP, unaryN, _provenancePkg, _localNamePkg⟩ := carrier
  have densityUnary : UnaryHistory densityRead :=
    unary_cont_closed unaryS unaryD densityRoute
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed densityUnary unaryF extensionRoute
  have namedUnary : UnaryHistory named :=
    unary_cont_closed extensionUnary unaryN namedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row F ∨ hsame row N ∨ hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S D densityRead ∧ Cont densityRead F extensionRead ∧
              Cont extensionRead N named ∧ PkgSig bundle named pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, densityRoute, extensionRoute, namedRoute, namedPkg⟩
  }
  exact ⟨cert, densityUnary, extensionUnary, namedUnary⟩

end BEDC.Derived.CauchyContinuousExtensionUp
