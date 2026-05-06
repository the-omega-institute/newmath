import BEDC.Derived.MatrixUp

namespace BEDC.Derived.MatrixUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem MatrixSingletonZero_additive_identity {A : BHist} :
    MatrixSingletonCarrier A ->
      hsame MatrixSingletonZero BHist.Empty ∧
        MatrixSingletonClassifier (MatrixSingletonAdd A MatrixSingletonZero) A ∧
          MatrixSingletonClassifier (MatrixSingletonAdd MatrixSingletonZero A) A ∧
            MatrixSingletonClassifier (append (MatrixSingletonAdd A MatrixSingletonZero) BHist.Empty)
              (append (MatrixSingletonAdd MatrixSingletonZero A) BHist.Empty) := by
  intro carrierA
  have zeroEmpty : hsame MatrixSingletonZero BHist.Empty := hsame_refl BHist.Empty
  have rightAddEmpty : hsame (MatrixSingletonAdd A MatrixSingletonZero) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro carrierA zeroEmpty)
  have leftAddEmpty : hsame (MatrixSingletonAdd MatrixSingletonZero A) BHist.Empty :=
    append_eq_empty_iff.mpr (And.intro zeroEmpty carrierA)
  have rightClassified : MatrixSingletonClassifier (MatrixSingletonAdd A MatrixSingletonZero) A :=
    And.intro rightAddEmpty
      (And.intro carrierA (hsame_trans rightAddEmpty (hsame_symm carrierA)))
  have leftClassified : MatrixSingletonClassifier (MatrixSingletonAdd MatrixSingletonZero A) A :=
    And.intro leftAddEmpty
      (And.intro carrierA (hsame_trans leftAddEmpty (hsame_symm carrierA)))
  have rightDisplayedEmpty :
      hsame (append (MatrixSingletonAdd A MatrixSingletonZero) BHist.Empty) BHist.Empty := by
    exact hsame_trans (append_empty_right (MatrixSingletonAdd A MatrixSingletonZero)) rightAddEmpty
  have leftDisplayedEmpty :
      hsame (append (MatrixSingletonAdd MatrixSingletonZero A) BHist.Empty) BHist.Empty := by
    exact hsame_trans (append_empty_right (MatrixSingletonAdd MatrixSingletonZero A)) leftAddEmpty
  have displayedClassified :
      MatrixSingletonClassifier (append (MatrixSingletonAdd A MatrixSingletonZero) BHist.Empty)
        (append (MatrixSingletonAdd MatrixSingletonZero A) BHist.Empty) :=
    And.intro rightDisplayedEmpty
      (And.intro leftDisplayedEmpty
        (hsame_trans rightDisplayedEmpty (hsame_symm leftDisplayedEmpty)))
  exact And.intro zeroEmpty
    (And.intro rightClassified (And.intro leftClassified displayedClassified))

end BEDC.Derived.MatrixUp
