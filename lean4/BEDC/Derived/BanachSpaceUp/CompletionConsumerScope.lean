import BEDC.Derived.BanachSpaceUp.CauchyWindowScope

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.BanachSpaceUp
