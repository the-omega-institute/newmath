import BEDC.Derived.MetricUp.RealDistancePublicLawPackage
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MetricspaceRealalgorderApartnessMetricNameCertRoute
    {x y dist radius witness budget classifier provenance realAlg visible : BHist} :
    MetricspaceRealDistanceCarrier x y dist radius witness budget classifier provenance realAlg →
      MetricDistanceWitness x y visible →
        hsame visible dist →
          SemanticNameCert
            (fun row : BHist => hsame row visible ∧ MetricDistanceWitness x y row)
            (fun row : BHist => hsame row visible ∧ UnaryHistory radius)
            (fun row : BHist =>
              hsame row visible ∧ Cont dist radius budget ∧ hsame classifier dist)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier visibleWitness _sameVisibleDist
  rcases carrier with
    ⟨distanceWitness, radiusUnary, distRadiusBudget, classifierSame,
      _witnessBudgetProvenance, _realAlgUnary⟩
  have visibleSource : hsame visible visible ∧ MetricDistanceWitness x y visible :=
    ⟨hsame_refl visible, visibleWitness⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro visible visibleSource
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, radiusUnary⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left,
          distRadiusBudget,
          classifierSame⟩
  }

end BEDC.Derived.MetricUp
