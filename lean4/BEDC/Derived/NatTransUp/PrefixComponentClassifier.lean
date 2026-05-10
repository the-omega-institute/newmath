import BEDC.Derived.NatTransUp
import BEDC.Derived.NatTransUp.EmptyComponentOpposite
import BEDC.Derived.NatTransUp.EmptyVertComp
import BEDC.Derived.NatTransUp.UnaryObjectSuffix
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

theorem NatTransPrefixComponentClassifier_component_semanticNameCert {p q a eta : BHist}
    (component : NatTransPrefixComponentCarrier p q a eta) :
    SemanticNameCert (NatTransPrefixComponentCarrier p q a)
      (NatTransPrefixComponentCarrier p q a) (NatTransPrefixComponentCarrier p q a)
      (NatTransPrefixComponentClassifier p q a) := by
  exact {
    core := {
      carrier_inhabited := Exists.intro eta component
      equiv_refl := by
        intro theta componentTheta
        exact
          And.intro componentTheta.left
            (And.intro componentTheta.right.left
              (And.intro componentTheta.right.right.left
                (And.intro componentTheta.right.right.right
                  (And.intro componentTheta.right.right.right (hsame_refl theta)))))
      equiv_symm := by
        intro theta iota classified
        exact
          And.intro classified.left
            (And.intro classified.right.left
              (And.intro classified.right.right.left
                (And.intro classified.right.right.right.right.left
                  (And.intro classified.right.right.right.left
                    (hsame_symm classified.right.right.right.right.right)))))
      equiv_trans := by
        intro theta iota kappa classifiedLeft classifiedRight
        exact
          And.intro classifiedLeft.left
            (And.intro classifiedLeft.right.left
              (And.intro classifiedLeft.right.right.left
                (And.intro classifiedLeft.right.right.right.left
                  (And.intro classifiedRight.right.right.right.right.left
                    (hsame_trans classifiedLeft.right.right.right.right.right
                      classifiedRight.right.right.right.right.right)))))
      carrier_respects_equiv := by
        intro theta iota classified _componentTheta
        exact
          And.intro classified.left
            (And.intro classified.right.left
              (And.intro classified.right.right.left
                classified.right.right.right.right.left))
    }
    pattern_sound := by
      intro _theta componentTheta
      exact componentTheta
    ledger_sound := by
      intro _theta componentTheta
      exact componentTheta
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

theorem NatTransPrefixComponentClassifier_hsame_transport
    {p p' q q' a a' eta eta' theta theta' : BHist} :
    hsame p p' -> hsame q q' -> hsame a a' -> hsame eta eta' -> hsame theta theta' ->
      NatTransPrefixComponentClassifier p q a eta theta ->
        NatTransPrefixComponentClassifier p' q' a' eta' theta' ∧
          CategoryHomCarrier (append p' a') (append q' a') eta' ∧
            CategoryHomCarrier (append p' a') (append q' a') theta' := by
  intro sameP sameQ sameA sameEta sameTheta classified
  have sourceSame : hsame (append p a) (append p' a') := by
    cases sameP
    cases sameA
    exact hsame_refl (append p a)
  have targetSame : hsame (append q a) (append q' a') := by
    cases sameQ
    cases sameA
    exact hsame_refl (append q a)
  have etaCarrier : CategoryHomCarrier (append p' a') (append q' a') eta' :=
    CategoryHomCarrier_hsame_transport sourceSame targetSame sameEta
      classified.right.right.right.left
  have thetaCarrier : CategoryHomCarrier (append p' a') (append q' a') theta' :=
    CategoryHomCarrier_hsame_transport sourceSame targetSame sameTheta
      classified.right.right.right.right.left
  have etaThetaSame : hsame eta' theta' :=
    hsame_trans (hsame_symm sameEta)
      (hsame_trans classified.right.right.right.right.right sameTheta)
  exact
    And.intro
      (And.intro (unary_transport classified.left sameP)
        (And.intro (unary_transport classified.right.left sameQ)
          (And.intro (unary_transport classified.right.right.left sameA)
          (And.intro etaCarrier (And.intro thetaCarrier etaThetaSame)))))
      (And.intro etaCarrier thetaCarrier)

theorem NatTransPrefixComponentClassifier_vert_comp_right_identity_closed
    {p q a eta eta' right right' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      Cont eta BHist.Empty right -> Cont eta' BHist.Empty right' ->
        NatTransPrefixComponentClassifier p q a right right' ∧ hsame right right' := by
  intro classified rightRel rightRel'
  have rightSame : hsame right eta :=
    cont_deterministic rightRel (cont_right_unit eta)
  have rightSame' : hsame right' eta' :=
    cont_deterministic rightRel' (cont_right_unit eta')
  have transported :=
    NatTransPrefixComponentClassifier_hsame_transport
      (p := p) (p' := p) (q := q) (q' := q) (a := a) (a' := a)
      (eta := eta) (eta' := right) (theta := eta') (theta' := right')
      (hsame_refl p) (hsame_refl q) (hsame_refl a)
      (hsame_symm rightSame) (hsame_symm rightSame') classified
  exact And.intro transported.left transported.left.right.right.right.right.right

theorem NatTransPrefixComponentClassifier_zero_headed_component_absurd
    {p q a eta theta : BHist} :
    NatTransPrefixComponentClassifier p q a eta theta ->
      ((∃ w : BHist, p = BHist.e0 w) ∨ (∃ w : BHist, q = BHist.e0 w) ∨
        (∃ w : BHist, a = BHist.e0 w) ∨ (∃ w : BHist, eta = BHist.e0 w) ∨
          (∃ w : BHist, theta = BHist.e0 w)) -> False := by
  intro classified zeroComponent
  cases zeroComponent with
  | inl prefixZero =>
      cases prefixZero with
      | intro w prefixEq =>
          cases prefixEq
          exact unary_no_zero_extension classified.left
  | inr rest =>
      cases rest with
      | inl targetPrefixZero =>
          cases targetPrefixZero with
          | intro w targetPrefixEq =>
              cases targetPrefixEq
              exact unary_no_zero_extension classified.right.left
      | inr rest =>
          cases rest with
          | inl objectZero =>
              cases objectZero with
              | intro w objectEq =>
                  cases objectEq
                  exact unary_no_zero_extension classified.right.right.left
          | inr rest =>
              cases rest with
              | inl etaZero =>
                  cases etaZero with
                  | intro w etaEq =>
                      cases etaEq
                      exact unary_no_zero_extension
                        classified.right.right.right.left.right.right.left
              | inr thetaZero =>
                  cases thetaZero with
                  | intro w thetaEq =>
                      cases thetaEq
                      exact unary_no_zero_extension
                        classified.right.right.right.right.left.right.right.left

theorem NatTransPrefixComponentClassifier_empty_component_opposite_closed
    {p q a eta theta : BHist} :
    NatTransPrefixComponentClassifier p q a eta theta ->
      hsame eta BHist.Empty -> hsame theta BHist.Empty ->
        NatTransPrefixComponentClassifier q p a eta theta := by
  intro classified etaEmpty thetaEmpty
  have etaComponent : NatTransPrefixComponentCarrier p q a eta :=
    And.intro classified.left
      (And.intro classified.right.left
        (And.intro classified.right.right.left classified.right.right.right.left))
  have thetaComponent : NatTransPrefixComponentCarrier p q a theta :=
    And.intro classified.left
      (And.intro classified.right.left
        (And.intro classified.right.right.left classified.right.right.right.right.left))
  have etaOpposite : NatTransPrefixComponentCarrier q p a eta :=
    NatTransPrefixComponentCarrier_empty_component_opposite_closed etaComponent etaEmpty
  have thetaOpposite : NatTransPrefixComponentCarrier q p a theta :=
    NatTransPrefixComponentCarrier_empty_component_opposite_closed thetaComponent thetaEmpty
  exact
    And.intro etaOpposite.left
      (And.intro etaOpposite.right.left
        (And.intro etaOpposite.right.right.left
          (And.intro etaOpposite.right.right.right
            (And.intro thetaOpposite.right.right.right
              classified.right.right.right.right.right))))

theorem NatTransPrefixComponentClassifier_vert_comp_zero_headed_component_absurd
    {p q r a eta eta' theta theta' c c' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      NatTransPrefixComponentClassifier q r a theta theta' ->
        Cont eta theta c -> Cont eta' theta' c' ->
          ((∃ w : BHist, p = BHist.e0 w) ∨ (∃ w : BHist, q = BHist.e0 w) ∨
            (∃ w : BHist, r = BHist.e0 w) ∨ (∃ w : BHist, a = BHist.e0 w) ∨
              (∃ w : BHist, eta = BHist.e0 w) ∨ (∃ w : BHist, eta' = BHist.e0 w) ∨
                (∃ w : BHist, theta = BHist.e0 w) ∨
                  (∃ w : BHist, theta' = BHist.e0 w) ∨
                    (∃ w : BHist, c = BHist.e0 w) ∨
                      (∃ w : BHist, c' = BHist.e0 w)) -> False := by
  intro left right comp comp' zeroComponent
  have composite : NatTransPrefixComponentClassifier p r a c c' :=
    NatTransPrefixComponentClassifier_vert_comp_congr left right comp comp'
  cases zeroComponent with
  | inl pZero =>
      exact NatTransPrefixComponentClassifier_zero_headed_component_absurd left
        (Or.inl pZero)
  | inr rest =>
      cases rest with
      | inl qZero =>
          exact NatTransPrefixComponentClassifier_zero_headed_component_absurd left
            (Or.inr (Or.inl qZero))
      | inr rest =>
          cases rest with
          | inl rZero =>
              exact NatTransPrefixComponentClassifier_zero_headed_component_absurd right
                (Or.inr (Or.inl rZero))
          | inr rest =>
              cases rest with
              | inl aZero =>
                  exact NatTransPrefixComponentClassifier_zero_headed_component_absurd left
                    (Or.inr (Or.inr (Or.inl aZero)))
              | inr rest =>
                  cases rest with
                  | inl etaZero =>
                      exact NatTransPrefixComponentClassifier_zero_headed_component_absurd left
                        (Or.inr (Or.inr (Or.inr (Or.inl etaZero))))
                  | inr rest =>
                      cases rest with
                      | inl eta'Zero =>
                          exact NatTransPrefixComponentClassifier_zero_headed_component_absurd left
                            (Or.inr (Or.inr (Or.inr (Or.inr eta'Zero))))
                      | inr rest =>
                          cases rest with
                          | inl thetaZero =>
                              exact NatTransPrefixComponentClassifier_zero_headed_component_absurd
                                right (Or.inr (Or.inr (Or.inr (Or.inl thetaZero))))
                          | inr rest =>
                              cases rest with
                              | inl theta'Zero =>
                                  exact
                                    NatTransPrefixComponentClassifier_zero_headed_component_absurd
                                      right
                                      (Or.inr (Or.inr (Or.inr (Or.inr theta'Zero))))
                              | inr rest =>
                                  cases rest with
                                  | inl cZero =>
                                      exact
                                        NatTransPrefixComponentClassifier_zero_headed_component_absurd
                                          composite
                                          (Or.inr (Or.inr (Or.inr (Or.inl cZero))))
                                  | inr c'Zero =>
                                      exact
                                        NatTransPrefixComponentClassifier_zero_headed_component_absurd
                                          composite
                                          (Or.inr (Or.inr (Or.inr (Or.inr c'Zero))))

theorem NatTransPrefixComponentClassifier_vert_comp_empty_result_readback
    {p q r a eta eta' theta theta' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      NatTransPrefixComponentClassifier q r a theta theta' ->
        Cont eta theta BHist.Empty ->
          NatTransPrefixComponentClassifier p q a eta BHist.Empty ∧
            NatTransPrefixComponentClassifier q r a theta BHist.Empty ∧
              hsame p q ∧ hsame q r := by
  intro left right comp
  have leftCarrier : NatTransPrefixComponentCarrier p q a eta :=
    And.intro left.left
      (And.intro left.right.left
        (And.intro left.right.right.left left.right.right.right.left))
  have rightCarrier : NatTransPrefixComponentCarrier q r a theta :=
    And.intro right.left
      (And.intro right.right.left
        (And.intro right.right.right.left right.right.right.right.left))
  have emptyComponents :=
    NatTransPrefixComponentCarrier_vert_comp_empty_component_readback
      leftCarrier rightCarrier comp
  have emptyData :=
    Iff.mp (NatTransPrefixComponentCarrier_vert_comp_empty_iff leftCarrier rightCarrier) comp
  have leftClassified :
      NatTransPrefixComponentClassifier p q a eta BHist.Empty :=
    And.intro left.left
      (And.intro left.right.left
        (And.intro left.right.right.left
          (And.intro left.right.right.right.left
            (And.intro emptyComponents.left.right.right.right emptyData.left))))
  have rightClassified :
      NatTransPrefixComponentClassifier q r a theta BHist.Empty :=
    And.intro right.left
      (And.intro right.right.left
        (And.intro right.right.right.left
          (And.intro right.right.right.right.left
            (And.intro emptyComponents.right.left.right.right.right
              emptyData.right.left))))
  exact And.intro leftClassified
    (And.intro rightClassified
      (And.intro emptyComponents.right.right.left emptyComponents.right.right.right))

theorem NatTransPrefixComponentClassifier_vert_comp_empty_result_components
    {p q r a eta eta' theta theta' c c' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      NatTransPrefixComponentClassifier q r a theta theta' ->
        Cont eta theta c -> Cont eta' theta' c' -> hsame c BHist.Empty ->
          hsame c' BHist.Empty ->
            hsame eta BHist.Empty ∧ hsame eta' BHist.Empty ∧ hsame theta BHist.Empty ∧
              hsame theta' BHist.Empty ∧ hsame p q ∧ hsame q r := by
  intro left right comp comp' resultEmpty resultEmpty'
  have leftCarrier : NatTransPrefixComponentCarrier p q a eta :=
    And.intro left.left
      (And.intro left.right.left
        (And.intro left.right.right.left left.right.right.right.left))
  have rightCarrier : NatTransPrefixComponentCarrier q r a theta :=
    And.intro right.left
      (And.intro right.right.left
        (And.intro right.right.right.left right.right.right.right.left))
  have leftCarrier' : NatTransPrefixComponentCarrier p q a eta' :=
    And.intro left.left
      (And.intro left.right.left
        (And.intro left.right.right.left left.right.right.right.right.left))
  have rightCarrier' : NatTransPrefixComponentCarrier q r a theta' :=
    And.intro right.left
      (And.intro right.right.left
        (And.intro right.right.right.left right.right.right.right.right.left))
  have primaryData :=
    (NatTransPrefixComponentCarrier_vert_comp_result_empty_iff leftCarrier rightCarrier comp).mp
      resultEmpty
  have secondaryData :=
    (NatTransPrefixComponentCarrier_vert_comp_result_empty_iff leftCarrier' rightCarrier' comp').mp
      resultEmpty'
  exact And.intro primaryData.left
    (And.intro secondaryData.left
      (And.intro primaryData.right.left
        (And.intro secondaryData.right.left
          (And.intro primaryData.right.right.left primaryData.right.right.right))))

theorem NatTransPrefixComponentClassifier_vert_comp_empty_result_components_opposite_closed
    {p q r a eta eta' theta theta' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      NatTransPrefixComponentClassifier q r a theta theta' ->
        Cont eta theta BHist.Empty -> Cont eta' theta' BHist.Empty ->
          NatTransPrefixComponentClassifier q p a eta eta' ∧
            NatTransPrefixComponentClassifier r q a theta theta' := by
  intro left right comp comp'
  have componentData :
      hsame eta BHist.Empty ∧ hsame eta' BHist.Empty ∧ hsame theta BHist.Empty ∧
        hsame theta' BHist.Empty ∧ hsame p q ∧ hsame q r :=
    NatTransPrefixComponentClassifier_vert_comp_empty_result_components left right comp comp'
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  exact
    And.intro
      (NatTransPrefixComponentClassifier_empty_component_opposite_closed left
        componentData.left componentData.right.left)
      (NatTransPrefixComponentClassifier_empty_component_opposite_closed right
        componentData.right.right.left componentData.right.right.right.left)

theorem NatTransPrefixComponentClassifier_vert_comp_empty_result_cycle_closed
    {p q r a eta eta' theta theta' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      NatTransPrefixComponentClassifier q r a theta theta' ->
        Cont eta theta BHist.Empty -> Cont eta' theta' BHist.Empty ->
          NatTransPrefixComponentClassifier p r a BHist.Empty BHist.Empty ∧
            NatTransPrefixComponentClassifier r p a BHist.Empty BHist.Empty ∧
              hsame p q ∧ hsame q r ∧ hsame p r := by
  intro left right comp comp'
  have componentData :
      hsame eta BHist.Empty ∧ hsame eta' BHist.Empty ∧ hsame theta BHist.Empty ∧
        hsame theta' BHist.Empty ∧ hsame p q ∧ hsame q r :=
    NatTransPrefixComponentClassifier_vert_comp_empty_result_components left right comp comp'
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  have forward : NatTransPrefixComponentClassifier p r a BHist.Empty BHist.Empty :=
    NatTransPrefixComponentClassifier_vert_comp_congr left right comp comp'
  have backward : NatTransPrefixComponentClassifier r p a BHist.Empty BHist.Empty :=
    NatTransPrefixComponentClassifier_empty_component_opposite_closed forward
      (hsame_refl BHist.Empty) (hsame_refl BHist.Empty)
  exact And.intro forward
    (And.intro backward
      (And.intro componentData.right.right.right.right.left
        (And.intro componentData.right.right.right.right.right
          (hsame_trans componentData.right.right.right.right.left
            componentData.right.right.right.right.right))))

theorem NatTransPrefixComponentClassifier_empty_result_opposite_package
    {p q r a eta eta' theta theta' c c' : BHist} :
    NatTransPrefixComponentClassifier p q a eta eta' ->
      NatTransPrefixComponentClassifier q r a theta theta' ->
        Cont eta theta c -> Cont eta' theta' c' -> hsame c BHist.Empty ->
          hsame c' BHist.Empty ->
            NatTransPrefixComponentClassifier q p a eta eta' ∧
              NatTransPrefixComponentClassifier r q a theta theta' ∧ hsame p q ∧ hsame q r := by
  intro left right comp comp' resultEmpty resultEmpty'
  have componentData :
      hsame eta BHist.Empty ∧ hsame eta' BHist.Empty ∧ hsame theta BHist.Empty ∧
        hsame theta' BHist.Empty ∧ hsame p q ∧ hsame q r :=
    NatTransPrefixComponentClassifier_vert_comp_empty_result_components left right comp comp'
      resultEmpty resultEmpty'
  have leftOpposite : NatTransPrefixComponentClassifier q p a eta eta' :=
    NatTransPrefixComponentClassifier_empty_component_opposite_closed left
      componentData.left componentData.right.left
  have rightOpposite : NatTransPrefixComponentClassifier r q a theta theta' :=
    NatTransPrefixComponentClassifier_empty_component_opposite_closed right
      componentData.right.right.left componentData.right.right.right.left
  exact And.intro leftOpposite
    (And.intro rightOpposite
      (And.intro componentData.right.right.right.right.left
        componentData.right.right.right.right.right))

theorem NatTransPrefixComponentClassifier_stability_certificate_fields
    {p q r a eta eta' theta theta' c c' : BHist} :
    (forall {x : BHist}, NatTransPrefixComponentCarrier p q a x ->
      NatTransPrefixComponentClassifier p q a x x) ∧
      (NatTransPrefixComponentClassifier p q a eta eta' ->
        NatTransPrefixComponentClassifier p q a eta' eta) ∧
        (NatTransPrefixComponentClassifier p q a eta eta' ->
          NatTransPrefixComponentClassifier p q a eta' theta ->
            NatTransPrefixComponentClassifier p q a eta theta) ∧
          (hsame p q -> hsame eta eta' ->
            NatTransPrefixComponentClassifier p q a eta theta ->
              NatTransPrefixComponentClassifier q p a eta' theta) ∧
            (NatTransPrefixComponentClassifier p q a eta eta' ->
              NatTransPrefixComponentClassifier q r a theta theta' ->
                Cont eta theta c -> Cont eta' theta' c' ->
                  NatTransPrefixComponentClassifier p r a c c') := by
  have fields := NatTransPrefixComponentClassifier_equivalence_fields (p := p) (q := q) (a := a)
  exact
    And.intro fields.left
      (And.intro fields.right.left
        (And.intro fields.right.right.left
          (And.intro
            (fun samePQ sameEta classified =>
              (NatTransPrefixComponentClassifier_hsame_transport
                (p := p) (p' := q) (q := q) (q' := p) (a := a) (a' := a)
                (eta := eta) (eta' := eta') (theta := theta) (theta' := theta)
                samePQ (hsame_symm samePQ) (hsame_refl a) sameEta (hsame_refl theta)
                classified).left)
            (fun left right comp comp' =>
              NatTransPrefixComponentClassifier_vert_comp_congr left right comp comp'))))

theorem NatTransPrefixComponentClassifier_standard_bridge_fields {p q a eta theta : BHist} :
    NatTransPrefixComponentClassifier p q a eta theta ->
      UnaryHistory a ∧ CategoryHomCarrier p q eta ∧ CategoryHomCarrier p q theta ∧
        hsame eta theta := by
  intro classified
  have etaComponent : NatTransPrefixComponentCarrier p q a eta :=
    And.intro classified.left
      (And.intro classified.right.left
        (And.intro classified.right.right.left classified.right.right.right.left))
  have thetaComponent : NatTransPrefixComponentCarrier p q a theta :=
    And.intro classified.left
      (And.intro classified.right.left
        (And.intro classified.right.right.left classified.right.right.right.right.left))
  have etaData :=
    (NatTransPrefixComponentCarrier_unary_object_suffix_iff
      (p := p) (q := q) (a := a) (eta := eta)).mp etaComponent
  have thetaData :=
    (NatTransPrefixComponentCarrier_unary_object_suffix_iff
      (p := p) (q := q) (a := a) (eta := theta)).mp thetaComponent
  exact And.intro etaData.left
    (And.intro etaData.right
      (And.intro thetaData.right classified.right.right.right.right.right))

end BEDC.Derived.NatTransUp
