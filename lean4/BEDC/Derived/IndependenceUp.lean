import BEDC.FKernel.Cont
import BEDC.FKernel.Cont.Units
import BEDC.FKernel.Bundle

namespace BEDC.Derived.IndependenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Bundle

def IndependenceProductFold : ProbeBundle BHist -> BHist
  | ProbeBundle.Bnil => BHist.Empty
  | ProbeBundle.Bcons x xs => append x (IndependenceProductFold xs)

theorem IndependenceProductFold_bundleAppend (left right : ProbeBundle BHist) :
    hsame (IndependenceProductFold (bundleAppend left right))
      (append (IndependenceProductFold left) (IndependenceProductFold right)) := by
  induction left with
  | Bnil =>
      exact (append_empty_left (IndependenceProductFold right)).symm
  | Bcons x xs ih =>
      exact (congrArg (append x) ih).trans
        (append_assoc x (IndependenceProductFold xs) (IndependenceProductFold right)).symm

def IndependenceBinaryFactorization (joint left right product : BHist) : Prop :=
  Cont left right product ∧ hsame joint product

def IndependenceFiniteFactorizationRow
    (joint product : BHist) (marginals : ProbeBundle BHist) : Prop :=
  hsame (IndependenceProductFold marginals) BHist.Empty ∧
    Cont (IndependenceProductFold marginals) BHist.Empty product ∧ hsame joint product

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

theorem IndependenceFiniteReindexing_invariance
    {jointOriginal jointReindexed productOriginal productReindexed : BHist}
    {originalMarginals reindexedMarginals : ProbeBundle BHist} :
    (forall z : BHist, InBundle z originalMarginals <-> InBundle z reindexedMarginals) ->
      hsame (IndependenceProductFold originalMarginals) BHist.Empty ->
        IndependenceBinaryFactorization jointOriginal
          (IndependenceProductFold originalMarginals) BHist.Empty productOriginal ->
          hsame jointReindexed jointOriginal ->
            Cont (IndependenceProductFold reindexedMarginals) BHist.Empty productReindexed ->
              IndependenceBinaryFactorization jointReindexed
                (IndependenceProductFold reindexedMarginals) BHist.Empty productReindexed := by
  intro sameMembers originalFoldEmpty originalFactorization sameJoint reindexedProduct
  constructor
  · exact reindexedProduct
  · have reindexedFoldEmpty : hsame (IndependenceProductFold reindexedMarginals) BHist.Empty :=
      IndependenceFiniteProduct_reindexing_readback sameMembers originalFoldEmpty
    have originalProductOriginalFold :
        hsame productOriginal (IndependenceProductFold originalMarginals) :=
      cont_right_unit_result originalFactorization.left
    have originalProductEmpty : hsame productOriginal BHist.Empty :=
      hsame_trans originalProductOriginalFold originalFoldEmpty
    have originalJointEmpty : hsame jointOriginal BHist.Empty :=
      hsame_trans originalFactorization.right originalProductEmpty
    have reindexedJointEmpty : hsame jointReindexed BHist.Empty :=
      hsame_trans sameJoint originalJointEmpty
    have reindexedProductEmpty : hsame productReindexed BHist.Empty :=
      hsame_trans (cont_right_unit_result reindexedProduct) reindexedFoldEmpty
    exact hsame_trans reindexedJointEmpty (hsame_symm reindexedProductEmpty)

theorem IndependenceFiniteFactorizationRow_reindexing_closure
    {jointOriginal jointReindexed productOriginal productReindexed : BHist}
    {originalMarginals reindexedMarginals : ProbeBundle BHist} :
    (forall z : BHist, InBundle z originalMarginals <-> InBundle z reindexedMarginals) ->
      IndependenceFiniteFactorizationRow jointOriginal productOriginal originalMarginals ->
        hsame jointReindexed jointOriginal ->
          Cont (IndependenceProductFold reindexedMarginals) BHist.Empty productReindexed ->
            IndependenceFiniteFactorizationRow
              jointReindexed productReindexed reindexedMarginals := by
  intro sameMembers originalRow sameJoint reindexedProduct
  have reindexedFoldEmpty :
      hsame (IndependenceProductFold reindexedMarginals) BHist.Empty :=
    IndependenceFiniteProduct_reindexing_readback sameMembers originalRow.left
  have originalProductEmpty : hsame productOriginal BHist.Empty :=
    hsame_trans (cont_right_unit_result originalRow.right.left) originalRow.left
  have originalJointEmpty : hsame jointOriginal BHist.Empty :=
    hsame_trans originalRow.right.right originalProductEmpty
  have reindexedJointEmpty : hsame jointReindexed BHist.Empty :=
    hsame_trans sameJoint originalJointEmpty
  have reindexedProductEmpty : hsame productReindexed BHist.Empty :=
    hsame_trans (cont_right_unit_result reindexedProduct) reindexedFoldEmpty
  exact And.intro reindexedFoldEmpty
    (And.intro reindexedProduct
      (hsame_trans reindexedJointEmpty (hsame_symm reindexedProductEmpty)))

theorem IndependenceFiniteFactorizationRow_ledger_exactness
    {joint product : BHist} {marginals : ProbeBundle BHist} :
    IndependenceFiniteFactorizationRow joint product marginals ->
      hsame (IndependenceProductFold marginals) BHist.Empty ∧
        Cont (IndependenceProductFold marginals) BHist.Empty product ∧ hsame joint product ∧
          IndependenceBinaryFactorization joint
            (IndependenceProductFold marginals) BHist.Empty product := by
  intro row
  have binary :
      IndependenceBinaryFactorization joint
        (IndependenceProductFold marginals) BHist.Empty product :=
    And.intro row.right.left row.right.right
  exact And.intro row.left (And.intro row.right.left (And.intro row.right.right binary))

theorem IndependenceFiniteFactorizationRow_public_namecert_export
    {joint product : BHist} {marginals : ProbeBundle BHist} :
    IndependenceFiniteFactorizationRow joint product marginals ->
      hsame (IndependenceProductFold marginals) BHist.Empty ∧
        IndependenceBinaryFactorization joint (IndependenceProductFold marginals)
          BHist.Empty product ∧
        (∀ {joint' product' : BHist} {marginals' : ProbeBundle BHist},
          (∀ z : BHist, InBundle z marginals <-> InBundle z marginals') ->
            hsame joint' joint ->
              Cont (IndependenceProductFold marginals') BHist.Empty product' ->
                IndependenceFiniteFactorizationRow joint' product' marginals') := by
  intro row
  have exactness := IndependenceFiniteFactorizationRow_ledger_exactness row
  exact And.intro exactness.left
    (And.intro exactness.right.right.right
      (by
        intro joint' product' marginals' sameMembers sameJoint productCont
        exact IndependenceFiniteFactorizationRow_reindexing_closure
          sameMembers row sameJoint productCont))

end BEDC.Derived.IndependenceUp
