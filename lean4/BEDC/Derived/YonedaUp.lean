import BEDC.Derived.NatTransUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.YonedaUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Unary
open BEDC.FKernel.NameCert
open BEDC.Derived.NatTransUp

theorem YonedaRepresentable_empty_component_family_iff {p q : BHist} :
    ((forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty) <->
      UnaryHistory p /\ UnaryHistory q /\ hsame p q) := by
  constructor
  · intro familyCarrier
    have emptyComponent :
        NatTransPrefixComponentCarrier p q BHist.Empty BHist.Empty :=
      familyCarrier (a := BHist.Empty) unary_empty
    have data :=
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := q) (a := BHist.Empty)).mp emptyComponent
    exact And.intro data.left (And.intro data.right.left data.right.right.right)
  · intro data
    intro a objectCarrier
    exact
      (NatTransPrefixComponentCarrier_empty_identity_iff
        (p := p) (q := q) (a := a)).mpr
      (And.intro data.left
        (And.intro data.right.left
          (And.intro objectCarrier data.right.right)))

theorem YonedaRepresentable_empty_component_family_semanticNameCert {p : BHist}
    (prefixCarrier : UnaryHistory p) :
    SemanticNameCert
      (fun q : BHist => forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty)
      (fun q : BHist => forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty)
      (fun q : BHist => forall {a : BHist}, UnaryHistory a ->
        NatTransPrefixComponentCarrier p q a BHist.Empty)
      hsame := by
  constructor
  · constructor
    · exact Exists.intro p
        (by
          intro a objectCarrier
          exact
            (NatTransPrefixComponentCarrier_empty_identity_iff
              (p := p) (q := p) (a := a)).mpr
              (And.intro prefixCarrier
                (And.intro prefixCarrier
                  (And.intro objectCarrier (hsame_refl p)))))
    · intro q _familyCarrier
      exact hsame_refl q
    · intro q r sameQR
      exact hsame_symm sameQR
    · intro q r s sameQR sameRS
      exact hsame_trans sameQR sameRS
    · intro q r sameQR familyCarrier
      intro a objectCarrier
      cases sameQR
      exact familyCarrier objectCarrier
  · intro q source
    exact source
  · intro q source
    exact source

end BEDC.Derived.YonedaUp
