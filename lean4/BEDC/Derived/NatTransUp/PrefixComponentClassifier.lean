import BEDC.Derived.NatTransUp

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.Derived.CategoryUp

def NatTransPrefixComponentClassifier (p q a eta theta : BHist) : Prop :=
  UnaryHistory p ∧ UnaryHistory q ∧ UnaryHistory a ∧
    CategoryHomCarrier (append p a) (append q a) eta ∧
      CategoryHomCarrier (append p a) (append q a) theta ∧ hsame eta theta

theorem NatTransPrefixComponentClassifier_vert_comp_congr
    {p q r a eta eta' theta theta' c c' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      NatTransPrefixComponentClassifier q r a theta theta' ->
        Cont eta theta c -> Cont eta' theta' c' ->
          NatTransPrefixComponentClassifier p r a c c' := by
  intro left right comp comp'
  exact
    And.intro left.left
      (And.intro right.right.left
        (And.intro left.right.right.left
          (And.intro
            (CategoryHomCarrier_comp_closed left.right.right.right.left
              right.right.right.right.left comp)
            (And.intro
              (CategoryHomCarrier_comp_closed left.right.right.right.right.left
                right.right.right.right.right.left comp')
              (cont_respects_hsame left.right.right.right.right.right
                right.right.right.right.right.right comp comp')))))

theorem NatTransPrefixComponentClassifier_equivalence_fields {p q a : BHist} :
    (forall {eta : BHist}, NatTransPrefixComponentCarrier p q a eta ->
      NatTransPrefixComponentClassifier p q a eta eta) ∧
      (forall {eta theta : BHist}, NatTransPrefixComponentClassifier p q a eta theta ->
        NatTransPrefixComponentClassifier p q a theta eta) ∧
        (forall {eta theta iota : BHist},
          NatTransPrefixComponentClassifier p q a eta theta ->
            NatTransPrefixComponentClassifier p q a theta iota ->
              NatTransPrefixComponentClassifier p q a eta iota) ∧
          (forall {eta eta' : BHist}, NatTransPrefixComponentCarrier p q a eta ->
            hsame eta eta' -> NatTransPrefixComponentCarrier p q a eta' ∧
              CategoryHomCarrier (append p a) (append q a) eta') := by
  constructor
  · intro eta carrier
    exact And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right
            (And.intro carrier.right.right.right (hsame_refl eta)))))
  · constructor
    · intro eta theta classified
      exact And.intro classified.left
        (And.intro classified.right.left
          (And.intro classified.right.right.left
            (And.intro classified.right.right.right.right.left
              (And.intro classified.right.right.right.left
                (hsame_symm classified.right.right.right.right.right)))))
    · constructor
      · intro eta theta iota left right
        exact And.intro left.left
          (And.intro left.right.left
            (And.intro left.right.right.left
              (And.intro left.right.right.right.left
                (And.intro right.right.right.right.right.left
                  (hsame_trans left.right.right.right.right.right
                    right.right.right.right.right.right)))))
      · intro eta eta' carrier same
        have movedHom : CategoryHomCarrier (append p a) (append q a) eta' :=
          CategoryHomCarrier_hsame_transport (hsame_refl (append p a))
            (hsame_refl (append q a)) same carrier.right.right.right
        exact And.intro
          (And.intro carrier.left
            (And.intro carrier.right.left (And.intro carrier.right.right.left movedHom)))
          movedHom

end BEDC.Derived.NatTransUp
