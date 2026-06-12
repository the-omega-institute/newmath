import BEDC.Derived.BanachSpaceUp.CauchyWindowScope
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_completion_consumer_scope
    {V N M Q S R E Z H C P L vectorNormRead metricRead cauchyRead completionRead
      realSealRead separatedRead namedRead : BHist} :
    UnaryHistory V ->
      UnaryHistory N ->
        UnaryHistory M ->
          UnaryHistory Q ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory E ->
                  UnaryHistory Z ->
                    UnaryHistory L ->
                      Cont V N vectorNormRead ->
                        Cont vectorNormRead M metricRead ->
                          Cont M Q cauchyRead ->
                            Cont cauchyRead S completionRead ->
                              Cont completionRead R realSealRead ->
                                Cont realSealRead E separatedRead ->
                                  Cont separatedRead Z namedRead ->
                                    UnaryHistory vectorNormRead ∧
                                      UnaryHistory metricRead ∧
                                        UnaryHistory cauchyRead ∧
                                          UnaryHistory completionRead ∧
                                            UnaryHistory realSealRead ∧
                                              UnaryHistory separatedRead ∧
                                                UnaryHistory namedRead ∧
                                                  banachSpaceFields
                                                      (BanachSpaceUp.mk
                                                        V N M Q S R E Z H C P L) =
                                                    [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory BanachSpaceUp
  intro vUnary nUnary mUnary qUnary sUnary rUnary eUnary zUnary _lUnary vectorNormRoute
    metricRoute cauchyRoute completionRoute realSealRoute separatedRoute namedRoute
  have vectorNormUnary : UnaryHistory vectorNormRead :=
    unary_cont_closed vUnary nUnary vectorNormRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed vectorNormUnary mUnary metricRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed mUnary qUnary cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary sUnary completionRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed completionUnary rUnary realSealRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed realSealUnary eUnary separatedRoute
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed separatedUnary zUnary namedRoute
  exact
    ⟨vectorNormUnary, metricUnary, cauchyUnary, completionUnary, realSealUnary,
      separatedUnary, namedUnary, rfl⟩

theorem BanachSpaceNameCertObligations [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L vectorNormRead completionRead toleranceRead separatedRead
      replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory V ->
      UnaryHistory N ->
        UnaryHistory M ->
          UnaryHistory Q ->
            UnaryHistory S ->
              UnaryHistory R ->
                UnaryHistory E ->
                  UnaryHistory Z ->
                    UnaryHistory H ->
                      UnaryHistory C ->
                        Cont V N vectorNormRead ->
                          Cont M Q completionRead ->
                            Cont completionRead S toleranceRead ->
                              Cont toleranceRead E separatedRead ->
                                Cont separatedRead H replayRead ->
                                  PkgSig bundle P pkg ->
                                    PkgSig bundle L pkg ->
                                      SemanticNameCert
                                          (fun row : BHist =>
                                            hsame row replayRead ∧ UnaryHistory row)
                                          (fun row : BHist =>
                                            hsame row V ∨ hsame row N ∨ hsame row M ∨
                                              hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                                hsame row E ∨ hsame row Z ∨ hsame row H ∨
                                                  hsame row C ∨ hsame row P ∨
                                                    hsame row L ∨ hsame row replayRead)
                                          (fun row : BHist =>
                                            UnaryHistory row ∧ Cont V N vectorNormRead ∧
                                              Cont M Q completionRead ∧
                                                Cont completionRead S toleranceRead ∧
                                                  Cont toleranceRead E separatedRead ∧
                                                    Cont separatedRead H replayRead ∧
                                                      PkgSig bundle P pkg ∧
                                                        PkgSig bundle L pkg)
                                          hsame ∧
                                        banachSpaceFields
                                            (BanachSpaceUp.mk V N M Q S R E Z H C P L) =
                                          [V, N, M, Q, S, R, E, Z, H, C, P, L] := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro vUnary nUnary mUnary qUnary sUnary _rUnary eUnary _zUnary hUnary _cUnary
    vectorNormRoute completionRoute toleranceRoute separatedRoute replayRoute provenancePkg
    localPkg
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed mUnary qUnary completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary sUnary toleranceRoute
  have separatedUnary : UnaryHistory separatedRead :=
    unary_cont_closed toleranceUnary eUnary separatedRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed separatedUnary hUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row replayRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row Z ∨ hsame row H ∨ hsame row C ∨
                hsame row P ∨ hsame row L ∨ hsame row replayRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V N vectorNormRead ∧ Cont M Q completionRead ∧
              Cont completionRead S toleranceRead ∧ Cont toleranceRead E separatedRead ∧
                Cont separatedRead H replayRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro replayRead ⟨hsame_refl replayRead, replayUnary⟩
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
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr
                            (Or.inr
                              (Or.inr source.left)))))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, vectorNormRoute, completionRoute, toleranceRoute, separatedRoute,
          replayRoute, provenancePkg, localPkg⟩
  }
  exact ⟨cert, rfl⟩

end BEDC.Derived.BanachSpaceUp
