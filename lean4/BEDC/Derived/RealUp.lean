import BEDC.Derived.RatUp

namespace BEDC.Derived.RealUp

open BEDC.FKernel.Hist
open BEDC.Derived.RatUp

def RealConstantHistoryCarrier (h : BHist) : Prop :=
  ∃ d : BHist, hsame h (BHist.e1 d) ∧ RatHistoryCarrier d

def RealConstantHistoryClassifier (h k : BHist) : Prop :=
  ∃ d : BHist, ∃ e : BHist,
    hsame h (BHist.e1 d) ∧ hsame k (BHist.e1 e) ∧ RatHistoryClassifier d e

theorem RealConstantHistoryCarrier_e1_iff_rat {d : BHist} :
    RealConstantHistoryCarrier (BHist.e1 d) ↔ RatHistoryCarrier d := by
  constructor
  · intro carrier
    cases carrier with
    | intro witness data =>
        cases data with
        | intro same witnessCarrier =>
            exact RatHistoryCarrier_hsame_transport
              (hsame_symm (hsame_e1_iff.mp same)) witnessCarrier
  · intro ratCarrier
    exact ⟨d, hsame_refl (BHist.e1 d), ratCarrier⟩

theorem RealConstantHistoryClassifier_e1_iff_rat {d e : BHist} :
    RealConstantHistoryClassifier (BHist.e1 d) (BHist.e1 e) ↔
      RatHistoryClassifier d e := by
  constructor
  · intro classifier
    cases classifier with
    | intro dWitness rest =>
        cases rest with
        | intro eWitness data =>
            cases data with
            | intro sameD rest =>
                cases rest with
                | intro sameE ratClassifier =>
                    exact RatHistoryClassifier_hsame_transport
                      (hsame_symm (hsame_e1_iff.mp sameD))
                      (hsame_symm (hsame_e1_iff.mp sameE))
                      ratClassifier
  · intro ratClassifier
    exact ⟨d, e, hsame_refl (BHist.e1 d), hsame_refl (BHist.e1 e), ratClassifier⟩

end BEDC.Derived.RealUp
