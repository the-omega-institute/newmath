import BEDC.Derived.ListUp.FramedEndpoint

namespace BEDC.Derived.ListUp

open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def ListSingletonHistorySource (a0 : BHist) (h : BHist) : Prop :=
  hsame h a0

theorem ListSingletonHistorySource_framed_carrier_certificate {a0 : BHist} :
    SemanticNameCert
      (FramedListHistoryCarrier (ListSingletonHistorySource a0))
      (FramedListHistoryCarrier (ListSingletonHistorySource a0))
      (FramedListHistoryCarrier (ListSingletonHistorySource a0))
      (FramedListBridgeClassifier (ListSingletonHistorySource a0) hsame) := by
  have sourceCert : NameCert (ListSingletonHistorySource a0) hsame := by
    exact {
      carrier_inhabited := Exists.intro a0 (hsame_refl a0)
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro _h _k same
        exact hsame_symm same
      equiv_trans := by
        intro _h _k _r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro _h _k sameHK sourceH
        exact hsame_trans (hsame_symm sameHK) sourceH
    }
  have compat :
      ListSourceHsameCompatible (ListSingletonHistorySource a0) hsame := by
    intro _a _b _sourceA _sourceB same
    exact same
  exact FramedListBridgeClassifier_semantic_name_certificate sourceCert compat

end BEDC.Derived.ListUp
