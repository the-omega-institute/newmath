import BEDC.Derived.RegularCauchyCompletionCriterionUp.RealSealHandoff

namespace BEDC.Derived.RegularCauchyCompletionCriterionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyCompletionCriterionTransportStability [AskSetup] [PackageSetup]
    {R W D M L Q H C P N R' W' D' M' L' Q' H' C' P' N' finiteRead finiteRead'
      completionRead completionRead' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyCompletionCriterionCarrier R W D M L Q H C P N bundle pkg ->
      RegularCauchyCompletionCriterionCarrier R' W' D' M' L' Q' H' C' P' N' bundle pkg ->
        hsame W W' ->
          hsame D D' ->
            hsame Q Q' ->
              Cont W D finiteRead ->
                Cont finiteRead Q completionRead ->
                  Cont W' D' finiteRead' ->
                    Cont finiteRead' Q' completionRead' ->
                      PkgSig bundle completionRead pkg ->
                        PkgSig bundle completionRead' pkg ->
                          SemanticNameCert
                              (fun row : BHist =>
                                (hsame row completionRead ∨ hsame row completionRead') ∧
                                  UnaryHistory row)
                              (fun row : BHist =>
                                hsame row R ∨ hsame row W ∨ hsame row D ∨
                                  hsame row Q ∨ hsame row R' ∨ hsame row W' ∨
                                    hsame row D' ∨ hsame row Q' ∨
                                      hsame row completionRead ∨
                                        hsame row completionRead')
                              (fun row : BHist =>
                                UnaryHistory row ∧ hsame W W' ∧ hsame D D' ∧
                                  hsame Q Q' ∧ Cont W D finiteRead ∧
                                    Cont finiteRead Q completionRead ∧
                                      Cont W' D' finiteRead' ∧
                                        Cont finiteRead' Q' completionRead' ∧
                                          PkgSig bundle completionRead pkg ∧
                                            PkgSig bundle completionRead' pkg)
                              hsame ∧
                            UnaryHistory completionRead ∧ UnaryHistory completionRead' := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier carrier' sameW sameD sameQ finiteRoute completionRoute finiteRoute'
    completionRoute' completionPkg completionPkg'
  obtain ⟨_rUnary, wUnary, dUnary, _mUnary, _lUnary, qUnary, _hUnary, _cUnary,
    _pUnary, _nUnary, _pkgP, _pkgN⟩ := carrier
  obtain ⟨_rUnary', wUnary', dUnary', _mUnary', _lUnary', qUnary', _hUnary', _cUnary',
    _pUnary', _nUnary', _pkgP', _pkgN'⟩ := carrier'
  have finiteUnary : UnaryHistory finiteRead :=
    unary_cont_closed wUnary dUnary finiteRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed finiteUnary qUnary completionRoute
  have finiteUnary' : UnaryHistory finiteRead' :=
    unary_cont_closed wUnary' dUnary' finiteRoute'
  have completionUnary' : UnaryHistory completionRead' :=
    unary_cont_closed finiteUnary' qUnary' completionRoute'
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row completionRead ∨ hsame row completionRead') ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row R ∨ hsame row W ∨ hsame row D ∨ hsame row Q ∨ hsame row R' ∨
              hsame row W' ∨ hsame row D' ∨ hsame row Q' ∨ hsame row completionRead ∨
                hsame row completionRead')
          (fun row : BHist =>
            UnaryHistory row ∧ hsame W W' ∧ hsame D D' ∧ hsame Q Q' ∧
              Cont W D finiteRead ∧ Cont finiteRead Q completionRead ∧
                Cont W' D' finiteRead' ∧ Cont finiteRead' Q' completionRead' ∧
                  PkgSig bundle completionRead pkg ∧ PkgSig bundle completionRead' pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨Or.inl (hsame_refl completionRead), completionUnary⟩
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
        cases source.left with
        | inl sameCompletion =>
            exact
              ⟨Or.inl (hsame_trans (hsame_symm sameRows) sameCompletion),
                unary_transport source.right sameRows⟩
        | inr sameCompletion' =>
            exact
              ⟨Or.inr (hsame_trans (hsame_symm sameRows) sameCompletion'),
                unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameCompletion =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inl sameCompletion))))))))
      | inr sameCompletion' =>
          exact
            Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr sameCompletion'))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sameW, sameD, sameQ, finiteRoute, completionRoute, finiteRoute',
          completionRoute', completionPkg, completionPkg'⟩
  }
  exact ⟨cert, completionUnary, completionUnary'⟩

end BEDC.Derived.RegularCauchyCompletionCriterionUp
