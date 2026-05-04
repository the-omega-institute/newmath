import BEDC.Derived.NatTransUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.NatTransUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
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

theorem NatTransPrefixComponentClassifier_semanticNameCert {p q a : BHist}
    (emptyComponent : NatTransPrefixComponentCarrier p q a BHist.Empty) :
    SemanticNameCert (NatTransPrefixComponentCarrier p q a)
      (NatTransPrefixComponentCarrier p q a) (NatTransPrefixComponentCarrier p q a)
      (NatTransPrefixComponentClassifier p q a) := by
  exact {
    core := {
      carrier_inhabited := Exists.intro BHist.Empty emptyComponent
      equiv_refl := by
        intro eta component
        exact
          And.intro component.left
            (And.intro component.right.left
              (And.intro component.right.right.left
                (And.intro component.right.right.right
                  (And.intro component.right.right.right (hsame_refl eta)))))
      equiv_symm := by
        intro eta theta classified
        exact
          And.intro classified.left
            (And.intro classified.right.left
              (And.intro classified.right.right.left
                (And.intro classified.right.right.right.right.left
                  (And.intro classified.right.right.right.left
                    (hsame_symm classified.right.right.right.right.right)))))
      equiv_trans := by
        intro eta theta iota classifiedLeft classifiedRight
        exact
          And.intro classifiedLeft.left
            (And.intro classifiedLeft.right.left
              (And.intro classifiedLeft.right.right.left
                (And.intro classifiedLeft.right.right.right.left
                  (And.intro classifiedRight.right.right.right.right.left
                    (hsame_trans classifiedLeft.right.right.right.right.right
                      classifiedRight.right.right.right.right.right)))))
      carrier_respects_equiv := by
        intro eta theta classified _component
        exact
          And.intro classified.left
            (And.intro classified.right.left
              (And.intro classified.right.right.left
                classified.right.right.right.right.left))
    }
    pattern_sound := by
      intro _eta component
      exact component
    ledger_sound := by
      intro _eta component
      exact component
  }

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
