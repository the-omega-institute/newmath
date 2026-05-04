import BEDC.Derived.RealUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

theorem RealConstantHistoryClassifier_equivalence_fields :
    (∀ {h : BHist}, RealConstantHistoryCarrier h → RealConstantHistoryClassifier h h) ∧
      (∀ {h k : BHist}, RealConstantHistoryClassifier h k → RealConstantHistoryClassifier k h) ∧
        (∀ {h k l : BHist}, RealConstantHistoryClassifier h k →
          RealConstantHistoryClassifier k l → RealConstantHistoryClassifier h l) := by
  constructor
  · intro h carrier
    cases carrier with
    | intro d data =>
        cases data with
        | intro sameHD ratCarrier =>
            exact ⟨d, d, sameHD, sameHD,
              And.intro ratCarrier (And.intro ratCarrier (hsame_refl d))⟩
  · constructor
    · intro h k classifier
      cases classifier with
      | intro d rest =>
          cases rest with
          | intro e data =>
              cases data with
              | intro sameHD rest =>
                  cases rest with
                  | intro sameKE ratClassifier =>
                      exact ⟨e, d, sameKE, sameHD, RatHistoryClassifier_symm ratClassifier⟩
    · intro h k l classifierHK classifierKL
      cases classifierHK with
      | intro d hkRest =>
          cases hkRest with
          | intro e hkData =>
              cases hkData with
              | intro sameHD hkRest =>
                  cases hkRest with
                  | intro sameKE ratDE =>
                      cases classifierKL with
                      | intro e' klRest =>
                          cases klRest with
                          | intro f klData =>
                              cases klData with
                              | intro sameKE' klRest =>
                                  cases klRest with
                                  | intro sameLF ratE'F =>
                                      have sameEE' : hsame e e' :=
                                        hsame_e1_iff.mp
                                          (hsame_trans (hsame_symm sameKE) sameKE')
                                      have ratEF : RatHistoryClassifier e f :=
                                        RatHistoryClassifier_hsame_transport
                                          (hsame_symm sameEE') (hsame_refl f) ratE'F
                                      exact ⟨d, f, sameHD, sameLF,
                                        RatHistoryClassifier_trans ratDE ratEF⟩

end BEDC.Derived.RealUp
