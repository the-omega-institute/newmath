import BEDC.Derived.StreamNameUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.Derived.RatUp

theorem RatStreamNameFiniteWindowClassifier_bundle_union_handoff {s t : BHist -> BHist}
    {left right : ProbeBundle BHist} :
    RatStreamNameFiniteWindowClassifier s t left ->
      RatStreamNameFiniteWindowClassifier s t right ->
        RatStreamNameFiniteWindowClassifier s t (bundleAppend left right) ∧
          (RatStreamNameFiniteWindowClassifier s t (bundleAppend left right) ->
            RatStreamNameFiniteWindowClassifier s t left ∧
              RatStreamNameFiniteWindowClassifier s t right) := by
  intro classifiedLeft classifiedRight
  constructor
  · intro n member nUnary
    cases Iff.mp inBundle_bundleAppend_iff member with
    | inl memberLeft =>
        exact classifiedLeft n memberLeft nUnary
    | inr memberRight =>
        exact classifiedRight n memberRight nUnary
  · intro classifiedUnion
    constructor
    · intro n memberLeft nUnary
      exact classifiedUnion n (Iff.mpr inBundle_bundleAppend_iff (Or.inl memberLeft))
        nUnary
    · intro n memberRight nUnary
      exact classifiedUnion n (Iff.mpr inBundle_bundleAppend_iff (Or.inr memberRight))
        nUnary

theorem StreamNameRegSeqRatPointwiseHandoff {s t : BHist -> BHist}
    {bundle : ProbeBundle BHist} :
    RatStreamNameCarrier s ->
      RatStreamNameCarrier t ->
        RatStreamNameFiniteWindowClassifier s t bundle ->
          (exists n : BHist, InBundle n bundle ∧ UnaryHistory n) ->
            SemanticNameCert
              (fun row : BHist =>
                exists n : BHist, InBundle n bundle ∧ UnaryHistory n ∧
                  hsame row (s n) ∧ RatHistoryCarrier row)
              (fun _row : BHist =>
                exists n : BHist, InBundle n bundle ∧ UnaryHistory n ∧
                  RatHistoryClassifier (s n) (t n))
              (fun _row : BHist =>
                exists n : BHist, InBundle n bundle ∧ UnaryHistory n ∧
                  RatHistoryClassifier (s n) (t n))
              (fun row row' : BHist => hsame row row') := by
  intro carrierS carrierT finiteWindow inhabitedWindow
  obtain ⟨n0, n0InBundle, n0Unary⟩ := inhabitedWindow
  have sourceWitness : RatHistoryCarrier (s n0) :=
    carrierS n0 n0Unary
  have _targetWitness : RatHistoryCarrier (t n0) :=
    carrierT n0 n0Unary
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro (s n0)
          ⟨n0, n0InBundle, n0Unary, hsame_refl (s n0), sourceWitness⟩
      equiv_refl := by
        intro row _sourceRow
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' classified
        exact hsame_symm classified
      equiv_trans := by
        intro _row _row' _row'' leftClassified rightClassified
        exact hsame_trans leftClassified rightClassified
      carrier_respects_equiv := by
        intro _row _row' classified sourceRow
        obtain ⟨n, nInBundle, nUnary, sameRowSource, rowCarrier⟩ := sourceRow
        exact
          ⟨n, nInBundle, nUnary, hsame_trans (hsame_symm classified) sameRowSource,
            RatHistoryCarrier_hsame_transport classified rowCarrier⟩
    }
    pattern_sound := by
      intro _row sourceRow
      obtain ⟨n, nInBundle, nUnary, _sameRowSource, _rowCarrier⟩ := sourceRow
      exact ⟨n, nInBundle, nUnary, finiteWindow n nInBundle nUnary⟩
    ledger_sound := by
      intro _row sourceRow
      obtain ⟨n, nInBundle, nUnary, _sameRowSource, _rowCarrier⟩ := sourceRow
      exact ⟨n, nInBundle, nUnary, finiteWindow n nInBundle nUnary⟩
  }

end BEDC.Derived.StreamNameUp
