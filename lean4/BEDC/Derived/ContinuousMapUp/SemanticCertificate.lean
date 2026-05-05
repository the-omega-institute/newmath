import BEDC.Derived.ContinuousMapUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.Derived.ContinuousUp

def ContinuousMapMetricPatternSpec (distance : BHist) : Prop :=
  ∃ source : BHist, ∃ map : BHist, ∃ target : BHist,
    ∃ modulus : BHist, ∃ cert : BHist,
      ContinuousMapCarrier source map target modulus cert distance ∧
        hsame distance (append source target)

theorem ContinuousMapMetricPatternSpec_carrier_readback
    {source map target modulus cert distance : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      ContinuousMapMetricPatternSpec distance ∧ hsame distance (append source target) := by
  intro carrier
  have exactness :
      ContinuousFunctionCarrier source map target modulus cert ∧
        hsame distance (append source target) :=
    ContinuousMapCarrier_canonical_distance_exactness.mp carrier
  constructor
  · exact
      Exists.intro source
        (Exists.intro map
          (Exists.intro target
            (Exists.intro modulus
              (Exists.intro cert (And.intro carrier exactness.right)))))
  · exact exactness.right

theorem continuousmap_semantic_name_certificate {source map target modulus cert : BHist}
    (carrier : ContinuousMapCarrier source map target modulus cert (append source target)) :
    SemanticNameCert (ContinuousMapCarrier source map target modulus cert)
      (ContinuousMapCarrier source map target modulus cert)
      (ContinuousMapCarrier source map target modulus cert) hsame := by
  constructor
  · constructor
    · exact Exists.intro (append source target) carrier
    · intro distance _carrier
      exact hsame_refl distance
    · intro distance distance' same
      exact hsame_symm same
    · intro distance distance' distance'' sameLeft sameRight
      exact hsame_trans sameLeft sameRight
    · intro distance distance' same displayed
      have displayedExact :
          ContinuousFunctionCarrier source map target modulus cert ∧
            hsame distance (append source target) :=
        ContinuousMapCarrier_canonical_distance_exactness.mp displayed
      exact
        ContinuousMapCarrier_canonical_distance_exactness.mpr
          (And.intro displayedExact.left
            (hsame_trans (hsame_symm same) displayedExact.right))
  · intro distance sourceCarrier
    exact sourceCarrier
  · intro distance sourceCarrier
    exact sourceCarrier

end BEDC.Derived.ContinuousMapUp
