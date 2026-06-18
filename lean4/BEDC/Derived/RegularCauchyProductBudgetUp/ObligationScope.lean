import BEDC.Derived.RegularCauchyProductBudgetUp.ProductClosureBudget

namespace BEDC.Derived.RegularCauchyProductBudgetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyProductBudget_obligation_scope [AskSetup] [PackageSetup]
    {A B WA WB DA DB D E R S H C P N windowA windowB dyadicA dyadicB publicRead
      obligationRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyProductBudgetCarrier A B WA WB DA DB D E R S H C P N bundle pkg →
      Cont A WA windowA →
        Cont B WB windowB →
          Cont windowA DA dyadicA →
            Cont windowB DB dyadicB →
              Cont DA DB D →
                Cont D E R →
                  Cont R S publicRead →
                    Cont publicRead H obligationRead →
                      PkgSig bundle D pkg →
                        PkgSig bundle E pkg →
                          PkgSig bundle R pkg →
                            PkgSig bundle publicRead pkg →
                              PkgSig bundle obligationRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row obligationRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row windowA ∨ hsame row windowB ∨
                                        hsame row dyadicA ∨ hsame row dyadicB ∨
                                          hsame row D ∨ hsame row E ∨
                                            hsame row R ∨ hsame row publicRead ∨
                                              hsame row obligationRead)
                                    (fun row : BHist =>
                                      hsame row obligationRead ∧
                                        Cont publicRead H obligationRead ∧
                                          PkgSig bundle obligationRead pkg)
                                    hsame ∧
                                  UnaryHistory windowA ∧ UnaryHistory windowB ∧
                                    UnaryHistory dyadicA ∧ UnaryHistory dyadicB ∧
                                      UnaryHistory D ∧ UnaryHistory E ∧
                                        UnaryHistory R ∧ UnaryHistory publicRead ∧
                                          UnaryHistory obligationRead ∧
                                            Cont DA DB D ∧ Cont D E R ∧
                                              Cont R S publicRead ∧
                                                Cont publicRead H obligationRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro carrier windowARoute windowBRoute dyadicARoute dyadicBRoute productRoute
    readbackRoute publicRoute obligationRoute _productPkg _budgetPkg _readbackPkg
    _publicPkg obligationPkg
  obtain ⟨aUnary, bUnary, waUnary, wbUnary, daUnary, dbUnary, dUnary, eUnary,
    _rUnary, sUnary, hUnary, _cUnary, _pUnary, _nUnary, _provenancePkg,
    _namePkg⟩ := carrier
  have windowAUnary : UnaryHistory windowA :=
    unary_cont_closed aUnary waUnary windowARoute
  have windowBUnary : UnaryHistory windowB :=
    unary_cont_closed bUnary wbUnary windowBRoute
  have dyadicAUnary : UnaryHistory dyadicA :=
    unary_cont_closed windowAUnary daUnary dyadicARoute
  have dyadicBUnary : UnaryHistory dyadicB :=
    unary_cont_closed windowBUnary dbUnary dyadicBRoute
  have rUnary : UnaryHistory R :=
    unary_cont_closed dUnary eUnary readbackRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed rUnary sUnary publicRoute
  have obligationUnary : UnaryHistory obligationRead :=
    unary_cont_closed publicUnary hUnary obligationRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row obligationRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row windowA ∨ hsame row windowB ∨ hsame row dyadicA ∨
              hsame row dyadicB ∨ hsame row D ∨ hsame row E ∨ hsame row R ∨
                hsame row publicRead ∨ hsame row obligationRead)
          (fun row : BHist =>
            hsame row obligationRead ∧ Cont publicRead H obligationRead ∧
              PkgSig bundle obligationRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro obligationRead ⟨hsame_refl obligationRead, obligationUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, obligationRoute, obligationPkg⟩
  }
  exact
    ⟨cert, windowAUnary, windowBUnary, dyadicAUnary, dyadicBUnary, dUnary,
      eUnary, rUnary, publicUnary, obligationUnary, productRoute, readbackRoute,
      publicRoute, obligationRoute⟩

end BEDC.Derived.RegularCauchyProductBudgetUp
