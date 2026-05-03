import BEDC.Derived.ContinuousUp
import BEDC.FKernel.Cont.Cancellation

namespace BEDC.Derived.ContinuousUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem ContinuousModulusChain_endpoint_cycle_moduli_empty
    {source first second target : BHist} :
    ContinuousModulusChain source first second target -> hsame source target ->
      hsame first BHist.Empty ∧ hsame second BHist.Empty := by
  intro chain sameEndpoint
  cases chain with
  | intro _sourceCarrier rest =>
      cases rest with
      | intro _firstCarrier rest =>
          cases rest with
          | intro _secondCarrier rest =>
              cases rest with
              | intro _targetCarrier witness =>
                  cases witness with
                  | intro middle middleData =>
                      cases middleData with
                      | intro firstRel secondRel =>
                          exact cont_mutual_extension_tails_empty firstRel
                            (cont_result_hsame_transport secondRel (hsame_symm sameEndpoint))

end BEDC.Derived.ContinuousUp
