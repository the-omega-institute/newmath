import BEDC.Derived.DecimalExpansionUp.TasteGate

namespace BEDC.Derived.DecimalExpansionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem DecimalExpansionDigitCarryDeterminacy
    {D W V Q R E Dp Wp Vp Qp Rp Ep prefixRead prefixReadp place placep dyadic dyadicp
      regseq regseqp sealRead sealReadp : BHist} :
    UnaryHistory D →
      UnaryHistory W →
        UnaryHistory V →
          UnaryHistory Q →
            UnaryHistory R →
              UnaryHistory E →
                UnaryHistory Dp →
                  UnaryHistory Wp →
                    UnaryHistory Vp →
                      UnaryHistory Qp →
                        UnaryHistory Rp →
                          UnaryHistory Ep →
                            Cont D W prefixRead →
                              Cont Dp Wp prefixReadp →
                                Cont prefixRead V place →
                                  Cont prefixReadp Vp placep →
                                    Cont place Q dyadic →
                                      Cont placep Qp dyadicp →
                                        Cont dyadic R regseq →
                                          Cont dyadicp Rp regseqp →
                                            Cont regseq E sealRead →
                                              Cont regseqp Ep sealReadp →
                                                hsame D Dp →
                                                  hsame W Wp →
                                                    hsame V Vp →
                                                      hsame Q Qp →
                                                        hsame R Rp →
                                                          hsame E Ep →
                                                            hsame regseq regseqp ∧
                                                              hsame sealRead sealReadp ∧
                                                                UnaryHistory regseq ∧
                                                                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro dUnary wUnary vUnary qUnary rUnary eUnary _dpUnary _wpUnary _vpUnary
    _qpUnary _rpUnary _epUnary prefixRoute prefixpRoute placeRoute placepRoute
    dyadicRoute dyadicpRoute regseqRoute regseqpRoute sealRoute sealpRoute sameD sameW
    sameV sameQ sameR sameE
  cases sameD
  cases sameW
  cases sameV
  cases sameQ
  cases sameR
  cases sameE
  cases prefixRoute
  cases prefixpRoute
  cases placeRoute
  cases placepRoute
  cases dyadicRoute
  cases dyadicpRoute
  cases regseqRoute
  cases regseqpRoute
  cases sealRoute
  cases sealpRoute
  have prefixUnary : UnaryHistory (append D W) :=
    unary_cont_closed dUnary wUnary rfl
  have placeUnary : UnaryHistory (append (append D W) V) :=
    unary_cont_closed prefixUnary vUnary rfl
  have dyadicUnary : UnaryHistory (append (append (append D W) V) Q) :=
    unary_cont_closed placeUnary qUnary rfl
  have regseqUnary : UnaryHistory (append (append (append (append D W) V) Q) R) :=
    unary_cont_closed dyadicUnary rUnary rfl
  have sealUnary :
      UnaryHistory (append (append (append (append (append D W) V) Q) R) E) :=
    unary_cont_closed regseqUnary eUnary rfl
  exact ⟨rfl, rfl, regseqUnary, sealUnary⟩

end BEDC.Derived.DecimalExpansionUp
