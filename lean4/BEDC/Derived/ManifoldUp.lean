import BEDC.FKernel.Cont
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

def ManifoldSingletonCarrier (h : BHist) : Prop :=
  hsame h BHist.Empty

theorem ManifoldSingletonCarrier_topology_scope {h : BHist} :
    ManifoldSingletonCarrier h -> hsame h BHist.Empty ∧ UnaryHistory h ∧ Cont BHist.Empty h h := by
  intro carrier
  exact And.intro carrier
    (And.intro (unary_transport unary_empty (hsame_symm carrier)) (cont_left_unit h))

theorem ManifoldSingleton_chart_value_transport {h k : BHist} :
    ManifoldSingletonCarrier h -> ManifoldSingletonCarrier k ->
      hsame h k ∧ UnaryHistory h ∧ UnaryHistory k ∧ Cont BHist.Empty h h ∧
        Cont BHist.Empty k k := by
  intro carrierH carrierK
  have hRows := ManifoldSingletonCarrier_topology_scope carrierH
  have kRows := ManifoldSingletonCarrier_topology_scope carrierK
  have sameHK : hsame h k := hsame_trans hRows.left (hsame_symm kRows.left)
  exact And.intro sameHK
    (And.intro hRows.right.left
      (And.intro kRows.right.left
        (And.intro hRows.right.right kRows.right.right)))

end BEDC.Derived.ManifoldUp
