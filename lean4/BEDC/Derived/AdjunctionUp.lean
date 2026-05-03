import BEDC.Derived.NatTransUp

namespace BEDC.Derived.AdjunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.NatTransUp

def AdjunctionUnitCounitCarrier (p q a unit counit composite : BHist) : Prop :=
  NatTransPrefixComponentCarrier p q a unit ∧
    NatTransPrefixComponentCarrier q p a counit ∧ Cont unit counit composite

theorem AdjunctionUnitCounitCarrier_empty_components_exact {p q a composite : BHist} :
    AdjunctionUnitCounitCarrier p q a BHist.Empty BHist.Empty composite ↔
      UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧ hsame p q ∧
        hsame composite BHist.Empty := by
  constructor
  · intro carrier
    have unitData :=
      (NatTransPrefixComponentCarrier_empty_identity_iff (p := p) (q := q) (a := a)).mp
        carrier.left
    exact
      And.intro unitData.left
        (And.intro unitData.right.left
          (And.intro unitData.right.right.left
            (And.intro unitData.right.right.right
              (cont_left_unit_result carrier.right.right))))
  · intro data
    cases data with
    | intro pCarrier rest =>
        cases rest with
        | intro qCarrier rest =>
            cases rest with
            | intro aCarrier rest =>
                cases rest with
                | intro samePQ compositeEmpty =>
                    exact
                      And.intro
                        ((NatTransPrefixComponentCarrier_empty_identity_iff
                          (p := p) (q := q) (a := a)).mpr
                          (And.intro pCarrier
                            (And.intro qCarrier (And.intro aCarrier samePQ))))
                        (And.intro
                          ((NatTransPrefixComponentCarrier_empty_identity_iff
                            (p := q) (q := p) (a := a)).mpr
                            (And.intro qCarrier
                              (And.intro pCarrier
                                (And.intro aCarrier (hsame_symm samePQ)))))
                          (cont_left_unit_iff.mpr compositeEmpty))

end BEDC.Derived.AdjunctionUp
