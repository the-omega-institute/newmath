import BEDC.Derived.LinearMapUp
import BEDC.FKernel.Unary

namespace BEDC.Derived.LinearMapUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LinearMapEvaluationGraphCompositionClosure
    {source middle target graphF graphG composite addF addG scalarF scalarG _pointwise
      _contRow _pkgRow _nameRow : BHist} :
    LinearMapSingletonCarrier source →
      LinearMapSingletonCarrier middle →
        LinearMapSingletonCarrier target →
          LinearMapSingletonCarrier graphF →
            LinearMapSingletonCarrier graphG →
              Cont graphF graphG composite →
                LinearMapSingletonClassifier middle middle →
                  LinearMapSingletonClassifier addF addG →
                    LinearMapSingletonClassifier scalarF scalarG →
                      LinearMapSingletonCarrier composite ∧
                        LinearMapSingletonClassifier composite BHist.Empty ∧
                          UnaryHistory composite := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro _sourceCarrier _middleCarrier _targetCarrier graphFCarrier graphGCarrier graphCont
    _middleClassifier _addClassifier _scalarClassifier
  have emptyCarrier : LinearMapSingletonCarrier BHist.Empty :=
    hsame_refl BHist.Empty
  have compositeCarrier : LinearMapSingletonCarrier composite :=
    cont_respects_hsame graphFCarrier graphGCarrier graphCont (cont_right_unit BHist.Empty)
  have compositeClassifier : LinearMapSingletonClassifier composite BHist.Empty :=
    ⟨compositeCarrier, emptyCarrier, compositeCarrier⟩
  have compositeUnary : UnaryHistory composite :=
    unary_transport unary_empty (hsame_symm compositeCarrier)
  exact ⟨compositeCarrier, compositeClassifier, compositeUnary⟩

end BEDC.Derived.LinearMapUp
