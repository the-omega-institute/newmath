import BEDC.Derived.RegularCauchyProductBudgetUp.Obligations
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudget_real_seal_boundary [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg →
      Cont D E R →
        Cont R S publicRead →
          PkgSig bundle R pkg →
            PkgSig bundle S pkg →
              PkgSig bundle publicRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                    (fun row : BHist => hsame row publicRead ∧ Cont D E R)
                    (fun row : BHist =>
                      hsame row publicRead ∧ Cont R S publicRead ∧
                        PkgSig bundle publicRead pkg)
                    hsame ∧
                  UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory publicRead ∧
                    Cont D E R ∧ Cont R S publicRead ∧ PkgSig bundle R pkg ∧
                      PkgSig bundle S pkg ∧ PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig UnaryHistory SemanticNameCert hsame
  intro carrier productRoute sealRoute readbackPkg sealPkg publicPkg
  obtain ⟨_aUnary, _bUnary, _waUnary, _wbUnary, _daUnary, _dbUnary, _dUnary,
    _eUnary, rUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg,
    _namePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rUnary sUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row publicRead ∧ Cont D E R)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont R S publicRead ∧
              PkgSig bundle publicRead pkg)
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
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, productRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, sealRoute, publicPkg⟩
  }
  exact
    ⟨cert, rUnary, sUnary, publicUnary, productRoute, sealRoute, readbackPkg,
      sealPkg, publicPkg⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
