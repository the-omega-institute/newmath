import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MatchingUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def MatchingEdgeSet
    (Vert Edge : BHist -> Prop) (Inc : BHist -> BHist -> Prop)
    (EdgeRel : BHist -> BHist -> Prop) (M : BHist -> Prop) : Prop :=
  (forall {e : BHist}, M e -> Edge e) ∧
    (forall {e e' v : BHist}, M e -> M e' -> Vert v -> Inc v e -> Inc v e' ->
      EdgeRel e e')

def FinSetEdgeSubset
    (Edge : BHist -> Prop) (EdgeRel : BHist -> BHist -> Prop)
    (bundle : ProbeBundle BHist) (N M : BHist -> Prop) : Prop :=
  (forall {e : BHist}, N e -> Edge e) ∧
    (forall {e : BHist}, N e -> exists q : BHist, InBundle q bundle ∧ EdgeRel e q) ∧
      (forall {e : BHist}, N e -> M e)

theorem MatchingEdgeSet_finite_subset_closed
    {Vert Edge : BHist -> Prop} {Inc : BHist -> BHist -> Prop}
    {EdgeRel : BHist -> BHist -> Prop} {bundle : ProbeBundle BHist} {M N : BHist -> Prop} :
    MatchingEdgeSet Vert Edge Inc EdgeRel M -> FinSetEdgeSubset Edge EdgeRel bundle N M ->
      MatchingEdgeSet Vert Edge Inc EdgeRel N := by
  intro matching subset
  cases matching with
  | intro _edgeRow incidentRow =>
      cases subset with
      | intro subsetEdgeRow subsetRest =>
          cases subsetRest with
          | intro bundleRow subsetRow =>
              constructor
              · intro e inN
                have _bundleWitness : exists q : BHist, InBundle q bundle ∧ EdgeRel e q :=
                  bundleRow inN
                exact subsetEdgeRow inN
              · intro e e' v inNE inNE' vertV incVE incVE'
                have _leftBundleWitness :
                    exists q : BHist, InBundle q bundle ∧ EdgeRel e q :=
                  bundleRow inNE
                have _rightBundleWitness :
                    exists q : BHist, InBundle q bundle ∧ EdgeRel e' q :=
                  bundleRow inNE'
                exact incidentRow (subsetRow inNE) (subsetRow inNE') vertV incVE incVE'

theorem MatchingEdgeSet_compatible_union_closed
    {Vert Edge : BHist -> Prop} {Inc EdgeRel : BHist -> BHist -> Prop}
    {M N : BHist -> Prop} :
    MatchingEdgeSet Vert Edge Inc EdgeRel M ->
      MatchingEdgeSet Vert Edge Inc EdgeRel N ->
        (forall {e e' v : BHist}, ((M e ∧ N e') ∨ (N e ∧ M e')) -> Vert v ->
          Inc v e -> Inc v e' -> EdgeRel e e') ->
          MatchingEdgeSet Vert Edge Inc EdgeRel (fun e : BHist => M e ∨ N e) := by
  intro matchingM matchingN crossCompatible
  cases matchingM with
  | intro edgeM incidentM =>
      cases matchingN with
      | intro edgeN incidentN =>
          constructor
          · intro e selected
            cases selected with
            | inl inM =>
                exact edgeM inM
            | inr inN =>
                exact edgeN inN
          · intro e e' v selectedE selectedE' vertV incVE incVE'
            cases selectedE with
            | inl inME =>
                cases selectedE' with
                | inl inME' =>
                    exact incidentM inME inME' vertV incVE incVE'
                | inr inNE' =>
                    exact crossCompatible (Or.inl (And.intro inME inNE')) vertV incVE incVE'
            | inr inNE =>
                cases selectedE' with
                | inl inME' =>
                    exact crossCompatible (Or.inr (And.intro inNE inME')) vertV incVE incVE'
                | inr inNE' =>
                    exact incidentN inNE inNE' vertV incVE incVE'

theorem MatchingEdgeSet_singleton_classifier_closed
    {Vert Edge : BHist -> Prop} {Inc EdgeRel : BHist -> BHist -> Prop}
    (edgeCert : NameCert Edge EdgeRel) {edgeStar : BHist} :
    Edge edgeStar ->
      MatchingEdgeSet Vert Edge Inc EdgeRel (fun edge : BHist => EdgeRel edge edgeStar) := by
  intro edgeCarrier
  constructor
  · intro edge selected
    have selectedBack : EdgeRel edgeStar edge :=
      NameCert.equiv_symm edgeCert selected
    exact NameCert.carrier_respects_equiv edgeCert selectedBack edgeCarrier
  · intro edge edge' _vertex selected selected' _vert _inc _inc'
    have selectedBack : EdgeRel edgeStar edge' :=
      NameCert.equiv_symm edgeCert selected'
    exact NameCert.equiv_trans edgeCert selected selectedBack

theorem MatchingEdgeSet_toggle_singleton_compatible_union_closed
    {Vert Edge : BHist -> Prop} {Inc EdgeRel : BHist -> BHist -> Prop}
    (edgeCert : NameCert Edge EdgeRel) {M : BHist -> Prop} {edgeStar : BHist} :
    MatchingEdgeSet Vert Edge Inc EdgeRel M ->
      Edge edgeStar ->
        (forall {e e' v : BHist}, ((M e ∧ EdgeRel e' edgeStar) ∨
          (EdgeRel e edgeStar ∧ M e')) -> Vert v -> Inc v e -> Inc v e' -> EdgeRel e e') ->
          MatchingEdgeSet Vert Edge Inc EdgeRel
            (fun edge : BHist => M edge ∨ EdgeRel edge edgeStar) := by
  intro matching edgeCarrier crossCompatible
  exact MatchingEdgeSet_compatible_union_closed matching
    (MatchingEdgeSet_singleton_classifier_closed edgeCert edgeCarrier) crossCompatible

theorem MatchingEdgeSet_e0_empty_absurd_predicate
    {Vert Edge : BHist -> Prop} {Inc : BHist -> BHist -> Prop}
    {EdgeRel : BHist -> BHist -> Prop} :
    MatchingEdgeSet Vert Edge Inc EdgeRel (fun e : BHist => hsame (BHist.e0 e) BHist.Empty) := by
  constructor
  · intro e selected
    exact False.elim (not_hsame_e0_empty selected)
  · intro e _e' _v selected _selected' _vert _inc _inc'
    exact False.elim (not_hsame_e0_empty selected)

end BEDC.Derived.MatchingUp
