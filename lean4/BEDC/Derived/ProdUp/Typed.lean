import BEDC.Derived.ProdUp

namespace BEDC.Derived.ProdUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def ProdTypedCarrier (Left Right : BHist -> Prop) (x : ProdCarrier BHist BHist) : Prop :=
  Left x.fst /\ Right x.snd

theorem ProdTypedCarrier_transport_from_source_certificates {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq)
    {x y : ProdCarrier BHist BHist} :
    ProdTypedCarrier Left Right x ->
      ProdClassifierSpec LeftEq RightEq x y ->
        ProdTypedCarrier Left Right y := by
  intro carrierX classified
  cases x with
  | mk xLeft xRight =>
      cases y with
      | mk yLeft yRight =>
          cases carrierX with
          | intro leftCarrier rightCarrier =>
              cases classified with
              | intro leftSame rightSame =>
                  constructor
                  · exact leftCert.carrier_respects_equiv leftSame leftCarrier
                  · exact rightCert.carrier_respects_equiv rightSame rightCarrier

theorem ProdClassifierSpec_symm_from_nameCert {Left Right : BHist -> Prop}
    {LeftEq RightEq : BHist -> BHist -> Prop}
    (leftCert : NameCert Left LeftEq) (rightCert : NameCert Right RightEq)
    {x y : ProdCarrier BHist BHist} :
    ProdClassifierSpec LeftEq RightEq x y -> ProdClassifierSpec LeftEq RightEq y x := by
  intro classified
  cases x with
  | mk xLeft xRight =>
      cases y with
      | mk yLeft yRight =>
          cases classified with
          | intro leftSame rightSame =>
              constructor
              · exact leftCert.equiv_symm leftSame
              · exact rightCert.equiv_symm rightSame

end BEDC.Derived.ProdUp
