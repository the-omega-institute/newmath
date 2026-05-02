import BEDC.FKernel.Hist

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Hist

def LinearMapSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

def LinearMapSingletonClassifier (h k : BHist) : Prop :=
  LinearMapSingletonCarrier h ∧ LinearMapSingletonCarrier k ∧ hsame h k

def LinearMapSingletonComp (_g _f : BHist) : BHist :=
  BHist.Empty

def LinearMapSingletonEval (_f _x : BHist) : BHist :=
  BHist.Empty

theorem LinearMapSingleton_public_empty_code_exactness {f g x : BHist} :
    LinearMapSingletonCarrier f -> LinearMapSingletonCarrier g ->
      LinearMapSingletonCarrier x ->
        LinearMapSingletonClassifier f BHist.Empty ∧
          LinearMapSingletonClassifier BHist.Empty BHist.Empty ∧
            LinearMapSingletonClassifier (LinearMapSingletonComp g f) BHist.Empty ∧
              LinearMapSingletonClassifier (LinearMapSingletonEval f x) x := by
  intro carrierF carrierG carrierX
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassifier : LinearMapSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact And.intro carrierF (And.intro emptyCarrier carrierF)
  · constructor
    · exact emptyClassifier
    · constructor
      · exact emptyClassifier
      · exact And.intro emptyCarrier (And.intro carrierX (hsame_symm carrierX))

end BEDC.Derived.LinearMapUp
