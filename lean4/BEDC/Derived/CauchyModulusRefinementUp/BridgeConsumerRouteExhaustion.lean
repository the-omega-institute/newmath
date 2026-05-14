import BEDC.Derived.CauchyModulusRefinementUp

namespace BEDC.Derived.CauchyModulusRefinementUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusRefinementCarrier_bridge_consumer_route_exhaustion
    [AskSetup] [PackageSetup]
    {m0 m1 u v t w q e h c p n tailBudget selected readback sealRead publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg →
      Cont m0 u tailBudget →
        Cont t w selected →
          Cont selected q readback →
            Cont readback e sealRead →
              Cont sealRead h publicRead →
                PkgSig bundle publicRead pkg →
                  UnaryHistory tailBudget ∧ UnaryHistory selected ∧
                    UnaryHistory readback ∧ UnaryHistory sealRead ∧
                      UnaryHistory publicRead ∧ Cont m0 u tailBudget ∧
                        Cont t w selected ∧ Cont selected q readback ∧
                          Cont readback e sealRead ∧ Cont sealRead h publicRead ∧
                            PkgSig bundle p pkg ∧ PkgSig bundle publicRead pkg ∧
                              hsame h n ∧
                                SemanticNameCert
                                  (fun row : BHist =>
                                    CauchyModulusRefinementCarrier
                                      m0 m1 u v t w q e h c p n bundle pkg ∧
                                      hsame row publicRead)
                                  (fun row : BHist =>
                                    Cont m0 u tailBudget ∧ Cont t w selected ∧
                                      Cont selected q readback ∧
                                        Cont readback e sealRead ∧ Cont sealRead h row)
                                  (fun row : BHist =>
                                    hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                                  hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier tailRoute selectedRoute readbackRoute sealRoute publicRoute publicPkg
  rcases carrier with
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have tailUnary : UnaryHistory tailBudget :=
    unary_cont_closed m0Unary uUnary tailRoute
  have selectedUnary : UnaryHistory selected :=
    unary_cont_closed tUnary wUnary selectedRoute
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed selectedUnary qUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary eUnary sealRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed sealReadUnary hUnary publicRoute
  have carrierSource :
      CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg :=
    ⟨m0Unary, m1Unary, uUnary, vUnary, tUnary, wUnary, qUnary, eUnary, hUnary, cUnary,
      pUnary, nUnary, m0m1u, uvt, twq, qeh, pPkg, hn⟩
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          CauchyModulusRefinementCarrier m0 m1 u v t w q e h c p n bundle pkg ∧
            hsame row publicRead)
        (fun row : BHist =>
          Cont m0 u tailBudget ∧ Cont t w selected ∧ Cont selected q readback ∧
            Cont readback e sealRead ∧ Cont sealRead h row)
        (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro publicRead (And.intro carrierSource (hsame_refl publicRead))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other same source
          exact And.intro source.left (hsame_trans (hsame_symm same) source.right)
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨tailRoute, selectedRoute, readbackRoute, sealRoute,
            cont_result_hsame_transport publicRoute (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact And.intro source.right publicPkg
    }
  exact
    ⟨tailUnary, selectedUnary, readbackUnary, sealReadUnary, publicReadUnary, tailRoute,
      selectedRoute, readbackRoute, sealRoute, publicRoute, pPkg, publicPkg, hn, cert⟩

end BEDC.Derived.CauchyModulusRefinementUp
