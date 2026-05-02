import BEDC.Derived.CategoryUp.Cycle

namespace BEDC.Derived.CategoryUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist

theorem ContinuationMorphism_prefix_cycle_tails_empty {p a b : BHist}
    (left : ContinuationMorphism (append p a) (append p b))
    (right : ContinuationMorphism b a) :
    hsame a b ∧ hsame left.tail BHist.Empty ∧ hsame right.tail BHist.Empty := by
  cases left with
  | mk leftTail leftRel =>
      cases right with
      | mk rightTail rightRel =>
          exact And.intro
            (cont_mutual_extension_hsame (cont_prefix_cancel leftRel) rightRel)
            (cont_mutual_extension_tails_empty (cont_prefix_cancel leftRel) rightRel)

theorem ContinuationMorphism_prefix_triangle_cycle_tails_empty {p a b c : BHist}
    (left : ContinuationMorphism (append p a) (append p b))
    (middle : ContinuationMorphism b c) (back : ContinuationMorphism c a) :
    hsame left.tail BHist.Empty ∧ hsame middle.tail BHist.Empty ∧
      hsame back.tail BHist.Empty ∧ hsame a b ∧ hsame b c := by
  cases left with
  | mk leftTail leftRel =>
      cases middle with
      | mk middleTail middleRel =>
          cases back with
          | mk backTail backRel =>
              have baseLeftRel : Cont a leftTail b := cont_prefix_cancel leftRel
              have compositeRel : Cont a (append leftTail middleTail) c := by
                cases baseLeftRel
                exact middleRel.trans (append_assoc a leftTail middleTail)
              have cycleTails :
                  hsame (append leftTail middleTail) BHist.Empty ∧
                    hsame backTail BHist.Empty :=
                cont_mutual_extension_tails_empty compositeRel backRel
              have emptyParts : leftTail = BHist.Empty ∧ middleTail = BHist.Empty :=
                append_eq_empty_iff.mp cycleTails.left
              cases emptyParts.left
              cases emptyParts.right
              exact
                And.intro (hsame_refl BHist.Empty)
                  (And.intro (hsame_refl BHist.Empty)
                    (And.intro cycleTails.right
                      (And.intro
                        (cont_deterministic (cont_right_unit a) baseLeftRel)
                        (cont_deterministic (cont_right_unit b) middleRel))))

theorem CategoryHomCarrier_unary_prefix_triangle_cycle_identity_carriers {p a b c f g h : BHist} :
    CategoryHomCarrier (append p a) (append p b) f -> CategoryHomCarrier b c g ->
      CategoryHomCarrier c a h ->
        CategoryHomCarrier a a BHist.Empty ∧ CategoryHomCarrier b b BHist.Empty ∧
          CategoryHomCarrier c c BHist.Empty ∧ hsame a b ∧ hsame b c := by
  intro left middle back
  have baseLeft : CategoryHomCarrier a b f :=
    (CategoryHomCarrier_unary_prefix_iff.mp left).right
  exact CategoryHomCarrier_triangle_cycle_identity_carriers baseLeft middle back

end BEDC.Derived.CategoryUp
