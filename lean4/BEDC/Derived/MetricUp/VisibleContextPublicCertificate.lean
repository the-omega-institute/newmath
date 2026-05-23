import BEDC.Derived.MetricUp.PublicDistanceSurface
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem MetricspacePublicDistanceSurface_visible_context_public_certificate
    {p q x y d budget provenance visible : BHist} :
    UnaryHistory p ->
      UnaryHistory q ->
        MetricspacePublicDistanceSurface x y d budget provenance ->
          MetricDistanceWitness (append p x) (append y q) visible ->
            hsame visible (append (append p d) q) ->
              SemanticNameCert
                (fun row : BHist =>
                  hsame row visible ∧ MetricDistanceWitness (append p x) (append y q) row)
                (fun row : BHist => hsame row visible)
                (fun row : BHist => hsame row visible ∧ UnaryHistory row)
                hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro pUnary qUnary surface visibleWitness sameVisible
  have visibleRows :=
    MetricspacePublicDistanceSurface_visible_context_consumer_surface
      pUnary qUnary surface visibleWitness sameVisible
  have visibleSource :
      MetricDistanceWitness (append p x) (append y q) visible := by
    cases sameVisible
    exact visibleRows.left
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro visible ⟨hsame_refl visible, visibleSource⟩
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
      exact source.left
    ledger_sound := by
      intro _row source
      exact And.intro source.left source.right.right.right.left
  }

end BEDC.Derived.MetricUp
