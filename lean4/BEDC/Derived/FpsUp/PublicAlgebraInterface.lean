import BEDC.Derived.FpsUp

namespace BEDC.Derived.FpsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert

theorem FpsRingup_public_algebra_interface :
    SemanticNameCert FpsSingletonCarrier FpsSingletonCarrier FpsSingletonCarrier
        FpsSingletonClassifier ∧
      FpsSingletonCarrier FpsSingletonZero ∧
      FpsSingletonCarrier FpsSingletonOne ∧
      (forall F G n : BHist,
        FpsSingletonClassifier (FpsSingletonPointwiseAdditionCoeff F G n) BHist.Empty) ∧
      (forall F G : BHist, FpsSingletonClassifier (FpsSingletonMul F G) BHist.Empty) := by
  have schema := fps_singleton_empty_schema_laws
  have emptyCarrier : FpsSingletonCarrier BHist.Empty := hsame_refl BHist.Empty
  have emptyClassified : FpsSingletonClassifier BHist.Empty BHist.Empty :=
    And.intro emptyCarrier (And.intro emptyCarrier (hsame_refl BHist.Empty))
  constructor
  · exact schema.left
  · constructor
    · exact schema.right.left
    · constructor
      · exact schema.right.right.left
      · constructor
        · intro F G n
          have pointwiseCarrier :
              FpsSingletonCarrier (FpsSingletonPointwiseAdditionCoeff F G n) :=
            append_eq_empty_iff.mpr (And.intro emptyCarrier emptyCarrier)
          exact And.intro pointwiseCarrier (And.intro emptyCarrier pointwiseCarrier)
        · intro F G
          exact emptyClassified

end BEDC.Derived.FpsUp
