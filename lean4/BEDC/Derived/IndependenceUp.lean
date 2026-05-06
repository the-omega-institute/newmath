import BEDC.FKernel.Cont
import BEDC.FKernel.Bundle

namespace BEDC.Derived.IndependenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Bundle

def IndependenceProductFold : ProbeBundle BHist -> BHist
  | ProbeBundle.Bnil => BHist.Empty
  | ProbeBundle.Bcons x xs => append x (IndependenceProductFold xs)

def IndependenceBinaryFactorization (joint left right product : BHist) : Prop :=
  Cont left right product ∧ hsame joint product

theorem IndependenceBinaryFactorization_measurable_image_bridge
    {jointOriginal jointImage marginalX marginalY imageMarginalX imageMarginalY
      productOriginal productImage : BHist} :
    IndependenceBinaryFactorization jointOriginal marginalX marginalY productOriginal ->
      hsame jointImage jointOriginal -> hsame imageMarginalX marginalX ->
        hsame imageMarginalY marginalY -> Cont imageMarginalX imageMarginalY productImage ->
          IndependenceBinaryFactorization jointImage imageMarginalX imageMarginalY productImage := by
  intro original sameJoint sameLeft sameRight imageProduct
  constructor
  · exact imageProduct
  · have sameProduct : hsame productOriginal productImage :=
      cont_respects_hsame (hsame_symm sameLeft) (hsame_symm sameRight)
        original.left imageProduct
    exact hsame_trans sameJoint (hsame_trans original.right sameProduct)

private theorem IndependenceFiniteProduct_reindexing_readback_entries_empty
    {xs : ProbeBundle BHist} :
    hsame (IndependenceProductFold xs) BHist.Empty ->
      forall z : BHist, InBundle z xs -> hsame z BHist.Empty := by
  intro xsEmpty z zInXs
  induction xs with
  | Bnil =>
      exact False.elim zInXs
  | Bcons x xtail ih =>
      cases zInXs with
      | inl sameZX =>
          have foldEmpty :
              append x (IndependenceProductFold xtail) = BHist.Empty := xsEmpty
          have xEmpty : hsame x BHist.Empty := (append_eq_empty_iff.mp foldEmpty).left
          cases sameZX
          exact xEmpty
      | inr zInTail =>
          have foldEmpty :
              append x (IndependenceProductFold xtail) = BHist.Empty := xsEmpty
          have tailEmpty : hsame (IndependenceProductFold xtail) BHist.Empty :=
            (append_eq_empty_iff.mp foldEmpty).right
          exact ih tailEmpty zInTail

private theorem IndependenceFiniteProduct_reindexing_readback_fold_empty
    {xs : ProbeBundle BHist} :
    (forall z : BHist, InBundle z xs -> hsame z BHist.Empty) ->
      hsame (IndependenceProductFold xs) BHist.Empty := by
  intro allEmpty
  induction xs with
  | Bnil =>
      rfl
  | Bcons x xtail ih =>
      have xEmpty : hsame x BHist.Empty := allEmpty x (Or.inl rfl)
      have tailMembers : forall z : BHist, InBundle z xtail -> hsame z BHist.Empty := by
        intro z zInTail
        exact allEmpty z (Or.inr zInTail)
      have tailEmpty : hsame (IndependenceProductFold xtail) BHist.Empty :=
        ih tailMembers
      exact append_eq_empty_iff.mpr (And.intro xEmpty tailEmpty)

theorem IndependenceFiniteProduct_reindexing_readback
    {xs ys : ProbeBundle BHist} :
    (forall z : BHist, InBundle z xs <-> InBundle z ys) ->
      hsame (IndependenceProductFold xs) BHist.Empty ->
        hsame (IndependenceProductFold ys) BHist.Empty := by
  intro sameMembers xsEmpty
  have allXsEmpty : forall z : BHist, InBundle z xs -> hsame z BHist.Empty := by
    exact IndependenceFiniteProduct_reindexing_readback_entries_empty xsEmpty
  have allYsEmpty : forall z : BHist, InBundle z ys -> hsame z BHist.Empty := by
    intro z zInYs
    exact allXsEmpty z ((sameMembers z).mpr zInYs)
  exact IndependenceFiniteProduct_reindexing_readback_fold_empty allYsEmpty

end BEDC.Derived.IndependenceUp
