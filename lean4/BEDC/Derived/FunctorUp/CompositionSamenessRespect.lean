import BEDC.FKernel.Cont

namespace BEDC.Derived.FunctorUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem FunctorComposition_preservation_sameness_respect_required
    {mappedComposite mappedPair compositeTarget : BHist}
    (rawPairLedger : Cont mappedPair BHist.Empty compositeTarget)
    (respectGap : hsame mappedComposite mappedPair -> False) :
    hsame mappedComposite compositeTarget -> False := by
  intro mappedSameTarget
  have targetSamePair : hsame compositeTarget mappedPair :=
    cont_deterministic rawPairLedger (cont_right_unit mappedPair)
  exact respectGap (hsame_trans mappedSameTarget targetSamePair)

end BEDC.Derived.FunctorUp
