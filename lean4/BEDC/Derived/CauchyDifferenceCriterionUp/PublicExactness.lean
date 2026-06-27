import BEDC.Derived.CauchyDifferenceCriterionUp.ObligationExport

namespace BEDC.Derived.CauchyDifferenceCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyDifferenceCriterionPublicExactness [AskSetup] [PackageSetup]
    {X Y D Z Q W T E H C P N diffRead nullRead zeroRead sealRead exportRead
      publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    cauchyDifferenceCriterionFields (CauchyDifferenceCriterionUp.mk X Y D Z Q W T E H C P N) =
        [X, Y, D, Z, Q, W, T, E, H, C, P, N] ->
      UnaryHistory D ->
        UnaryHistory Z ->
          UnaryHistory Q ->
            UnaryHistory E ->
              UnaryHistory N ->
                UnaryHistory C ->
                  Cont D Z diffRead ->
                    Cont diffRead Q nullRead ->
                      Cont nullRead E sealRead ->
                        Cont sealRead N exportRead ->
                          Cont exportRead C publicRead ->
                            PkgSig bundle P pkg ->
                              PkgSig bundle N pkg ->
                                PkgSig bundle exportRead pkg ->
                                  PkgSig bundle publicRead pkg ->
                                    SemanticNameCert
                                        (fun row : BHist =>
                                          hsame row publicRead ∧ UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row X ∨ hsame row Y ∨ hsame row D ∨
                                            hsame row Z ∨ hsame row Q ∨ hsame row W ∨
                                              hsame row T ∨ hsame row E ∨ hsame row N ∨
                                                hsame row diffRead ∨ hsame row nullRead ∨
                                                  hsame row sealRead ∨ hsame row exportRead ∨
                                                    hsame row publicRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont D Z diffRead ∧
                                            Cont diffRead Q nullRead ∧
                                              Cont nullRead E sealRead ∧
                                                Cont sealRead N exportRead ∧
                                                  Cont exportRead C publicRead ∧
                                                    PkgSig bundle publicRead pkg)
                                        hsame ∧
                                      UnaryHistory diffRead ∧ UnaryHistory nullRead ∧
                                        UnaryHistory sealRead ∧ UnaryHistory exportRead ∧
                                          UnaryHistory publicRead := by
  -- BEDC touchpoint anchor: CauchyDifferenceCriterionUp BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro fields_eq dUnary zUnary qUnary eUnary nUnary cUnary diffRoute nullRoute sealRoute
    exportRoute publicRoute _pPkg _nPkg _exportPkg publicPkg
  have _zeroReadRow : BHist := zeroRead
  cases fields_eq
  have diffReadUnary : UnaryHistory diffRead :=
    unary_cont_closed dUnary zUnary diffRoute
  have nullReadUnary : UnaryHistory nullRead :=
    unary_cont_closed diffReadUnary qUnary nullRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed nullReadUnary eUnary sealRoute
  have exportReadUnary : UnaryHistory exportRead :=
    unary_cont_closed sealReadUnary nUnary exportRoute
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed exportReadUnary cUnary publicRoute
  have sourcePublic :
      (fun row : BHist => hsame row publicRead ∧ UnaryHistory row) publicRead := by
    exact ⟨hsame_refl publicRead, publicReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row X ∨ hsame row Y ∨ hsame row D ∨ hsame row Z ∨ hsame row Q ∨
              hsame row W ∨ hsame row T ∨ hsame row E ∨ hsame row N ∨
                hsame row diffRead ∨ hsame row nullRead ∨ hsame row sealRead ∨
                  hsame row exportRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D Z diffRead ∧ Cont diffRead Q nullRead ∧
              Cont nullRead E sealRead ∧ Cont sealRead N exportRead ∧
                Cont exportRead C publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourcePublic
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
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      apply Or.inr
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, diffRoute, nullRoute, sealRoute, exportRoute, publicRoute,
          publicPkg⟩
  }
  exact
    ⟨cert, diffReadUnary, nullReadUnary, sealReadUnary, exportReadUnary,
      publicReadUnary⟩

end BEDC.Derived.CauchyDifferenceCriterionUp
