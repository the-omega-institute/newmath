import BEDC.Derived.MetricUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.MetricUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary

theorem MetricDistanceWitness_visible_context_semanticNameCert {p q x y : BHist} :
    UnaryHistory p -> UnaryHistory q -> UnaryHistory x -> UnaryHistory y ->
      BEDC.FKernel.NameCert.SemanticNameCert
        (fun d : BHist =>
          MetricDistanceWitness (append p x) (append y q) (append (append p d) q))
        (fun d : BHist =>
          MetricDistanceWitness (append p x) (append y q) (append (append p d) q))
        (fun d : BHist =>
          MetricDistanceWitness (append p x) (append y q) (append (append p d) q))
        hsame := by
  intro pCarrier qCarrier xCarrier yCarrier
  have central :
      MetricDistanceWitness x y (append x y) :=
    And.intro xCarrier
      (And.intro yCarrier
        (And.intro (unary_append_closed xCarrier yCarrier) (cont_intro rfl)))
  have visible :
      MetricDistanceWitness (append p x) (append y q) (append (append p (append x y)) q) :=
    (MetricDistanceWitness_visible_context_iff (p := p) (q := q) (x := x) (y := y)
      (d := append x y)).mpr
      (And.intro pCarrier (And.intro qCarrier central))
  constructor
  · constructor
    · exact Exists.intro (append x y) visible
    · intro d _witness
      exact hsame_refl d
    · intro d e same
      exact hsame_symm same
    · intro d e f sameDE sameEF
      exact hsame_trans sameDE sameEF
    · intro d e same witness
      cases same
      exact witness
  · intro d source
    exact source
  · intro d source
    exact source

end BEDC.Derived.MetricUp
