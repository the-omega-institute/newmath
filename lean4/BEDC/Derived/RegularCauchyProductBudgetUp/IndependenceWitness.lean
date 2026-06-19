import BEDC.Derived.RegularCauchyProductBudgetUp.Obligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudget_independence_witness [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB productRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg ->
      Cont A WA windowA ->
        Cont B WB windowB ->
          Cont DA DB D ->
            Cont D E productRead ->
              Cont productRead S publicRead ->
                PkgSig bundle D pkg ->
                  PkgSig bundle E pkg ->
                    PkgSig bundle publicRead pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row windowA ∨ hsame row windowB ∨ hsame row D ∨
                              hsame row E ∨ hsame row publicRead)
                          (fun row : BHist =>
                            hsame row publicRead ∧ Cont DA DB D ∧
                              Cont D E productRead ∧ Cont productRead S publicRead ∧
                                PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory windowA ∧ UnaryHistory windowB ∧
                          UnaryHistory D ∧ UnaryHistory E ∧ UnaryHistory productRead ∧
                            UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert
  intro carrier windowARoute windowBRoute dyadicProductRoute productReadRoute
    publicReadRoute productPkg budgetPkg publicPkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, dUnary, eUnary,
    _rUnary, sUnary, _hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg,
    _namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed aUnary waUnary windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed bUnary wbUnary windowBRoute
  have productDUnary : UnaryHistory D :=
    unary_cont_closed daUnary dbUnary dyadicProductRoute
  have productReadUnary : UnaryHistory productRead :=
    unary_cont_closed productDUnary eUnary productReadRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed productReadUnary sUnary publicReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row D ∨ hsame row E ∨
              hsame row publicRead)
          (fun row : BHist =>
            hsame row publicRead ∧ Cont DA DB D ∧ Cont D E productRead ∧
              Cont productRead S publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro publicRead ⟨hsame_refl publicRead, publicReadUnary⟩
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
        intro row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, dyadicProductRoute, productReadRoute, publicReadRoute, publicPkg⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, productDUnary, eUnary, productReadUnary,
      publicReadUnary⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
