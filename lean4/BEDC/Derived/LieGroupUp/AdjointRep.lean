import BEDC.Derived.LieGroupUp

namespace BEDC.Derived.LieGroupUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LieGroupSingleton_adjointrep_source_surface {s t x tangent chart : BHist} :
    LieGroupSingletonCarrier s -> LieGroupSingletonCarrier t -> LieGroupSingletonCarrier x ->
      BEDC.Derived.LieAlgebraUp.LieAlgebraSingletonCarrier tangent ->
        Cont BHist.Empty tangent chart ->
          LieGroupSingletonClassifier
              (LieGroupSingletonConjugationAction s
                (LieGroupSingletonConjugationAction t x))
              (LieGroupSingletonConjugationAction (append s t) x) ∧
            BEDC.Derived.LieAlgebraUp.LieAlgebraSingletonCarrier chart ∧
              hsame chart BHist.Empty ∧ UnaryHistory chart := by
  intro carrierS carrierT carrierX tangentCarrier chartRow
  have actionClassified :
      LieGroupSingletonClassifier
        (LieGroupSingletonConjugationAction s (LieGroupSingletonConjugationAction t x))
        (LieGroupSingletonConjugationAction (append s t) x) :=
    LieGroupSingleton_conjugation_action_law carrierS carrierT carrierX
  have readback :
      BEDC.Derived.LieAlgebraUp.LieAlgebraSingletonCarrier chart ∧
        hsame chart BHist.Empty ∧ UnaryHistory chart :=
    LieGroupSingleton_adjoint_readback carrierS tangentCarrier chartRow
  exact And.intro actionClassified readback

end BEDC.Derived.LieGroupUp
