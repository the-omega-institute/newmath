import BEDC.Derived.CauchyRateRealizationUp.RealSealRoute

namespace BEDC.Derived.CauchyRateRealizationUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem CauchyRateRealizationPublicCertificate
    {p r d s q m e H C P N rateRead windowRead toleranceRead readbackRead modulusRead sealRead
      publicRead : BHist} :
    UnaryHistory p →
      UnaryHistory r →
        UnaryHistory s →
          UnaryHistory d →
            UnaryHistory q →
              UnaryHistory m →
                UnaryHistory e →
                  UnaryHistory N →
                    Cont p r rateRead →
                      Cont rateRead s windowRead →
                        Cont windowRead d toleranceRead →
                          Cont toleranceRead q readbackRead →
                            Cont readbackRead m modulusRead →
                              Cont modulusRead e sealRead →
                                Cont sealRead N publicRead →
                                  UnaryHistory rateRead ∧ UnaryHistory windowRead ∧
                                    UnaryHistory toleranceRead ∧ UnaryHistory readbackRead ∧
                                      UnaryHistory modulusRead ∧ UnaryHistory sealRead ∧
                                        UnaryHistory publicRead ∧ Cont p r rateRead ∧
                                          Cont rateRead s windowRead ∧
                                            Cont windowRead d toleranceRead ∧
                                              Cont toleranceRead q readbackRead ∧
                                                Cont readbackRead m modulusRead ∧
                                                  Cont modulusRead e sealRead ∧
                                                    Cont sealRead N publicRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro pUnary rUnary sUnary dUnary qUnary mUnary eUnary nUnary rateRoute windowRoute
    toleranceRoute readbackRoute modulusRoute sealRoute publicRoute
  have sealChain :
      UnaryHistory rateRead ∧ UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
        UnaryHistory readbackRead ∧ UnaryHistory modulusRead ∧ UnaryHistory sealRead ∧
          Cont p r rateRead ∧ Cont rateRead s windowRead ∧
            Cont windowRead d toleranceRead ∧ Cont toleranceRead q readbackRead ∧
              Cont readbackRead m modulusRead ∧ Cont modulusRead e sealRead :=
    CauchyRateRealizationRealSealRoute (H := H) (C := C) (P := P) (N := N) pUnary
      rUnary sUnary dUnary qUnary mUnary eUnary rateRoute windowRoute toleranceRoute
      readbackRoute modulusRoute sealRoute
  exact
    ⟨sealChain.left, sealChain.right.left, sealChain.right.right.left,
      sealChain.right.right.right.left, sealChain.right.right.right.right.left,
      sealChain.right.right.right.right.right.left,
      unary_cont_closed sealChain.right.right.right.right.right.left nUnary publicRoute,
      sealChain.right.right.right.right.right.right.left,
      sealChain.right.right.right.right.right.right.right.left,
      sealChain.right.right.right.right.right.right.right.right.left,
      sealChain.right.right.right.right.right.right.right.right.right.left,
      sealChain.right.right.right.right.right.right.right.right.right.right.left,
      sealChain.right.right.right.right.right.right.right.right.right.right.right,
      publicRoute⟩

end BEDC.Derived.CauchyRateRealizationUp
