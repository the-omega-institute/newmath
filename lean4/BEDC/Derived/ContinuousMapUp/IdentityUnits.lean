import BEDC.Derived.ContinuousMapUp

namespace BEDC.Derived.ContinuousMapUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont

theorem ContinuousMapCarrier_empty_identities_two_sided_composition_units
    {source target map modulus cert distance displayedL displayedR : BHist} :
    ContinuousMapCarrier source map target modulus cert distance ->
      ContinuousMapCarrier source map target modulus cert (append source target) ∧
        ContinuousMapCarrier source map target modulus cert (append source target) ∧
          (ContinuousMapCarrier source map target modulus cert displayedL ->
            hsame displayedL (append source target)) ∧
            (ContinuousMapCarrier source map target modulus cert displayedR ->
              hsame displayedR (append source target)) := by
  intro carrier
  have identities := ContinuousMapCarrier_empty_identities_closed carrier
  have certRel : Cont target modulus cert := carrier.left.right.right.right.right.right
  have leftComposite :
      ContinuousMapCarrier source map target modulus cert (append source target) :=
    ContinuousMapCarrier_comp_closed identities.left carrier
      (cont_left_unit map) (cont_left_unit modulus) certRel
  have rightComposite :
      ContinuousMapCarrier source map target modulus cert (append source target) :=
    ContinuousMapCarrier_comp_closed carrier identities.right
      (cont_right_unit map) (cont_right_unit modulus) certRel
  exact
    And.intro leftComposite
      (And.intro rightComposite
        (And.intro
          (fun displayed =>
            (ContinuousMapCarrier_target_cert_distance_deterministic displayed
              leftComposite).right.right.left)
          (fun displayed =>
            (ContinuousMapCarrier_target_cert_distance_deterministic displayed
              rightComposite).right.right.left)))

end BEDC.Derived.ContinuousMapUp
