import BEDC.FKernel.Bundle
import BEDC.FKernel.Hist

namespace BEDC.Derived.MatchingUp

open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist

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

end BEDC.Derived.MatchingUp
