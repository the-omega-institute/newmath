import BEDC.Derived.GroupUp
import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.LieGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Unary

theorem LieGroupSingleton_operation_smoothness_obligation {h k product domain value : BHist} :
    GroupSingletonCarrier h ->
      GroupSingletonCarrier k ->
      Cont h k product ->
      Cont BHist.Empty product domain ->
      Cont product BHist.Empty value ->
        hsame product BHist.Empty ∧ ManifoldSingletonCarrier product ∧
          hsame (GroupSingletonInv h) BHist.Empty ∧
            ManifoldSingletonCarrier (GroupSingletonInv h) ∧ hsame domain BHist.Empty ∧
              hsame value BHist.Empty ∧ UnaryHistory value := by
  intro carrierH carrierK productReadback domainReadback valueReadback
  have productEmpty : hsame product BHist.Empty :=
    cont_respects_hsame carrierH carrierK productReadback (cont_left_unit BHist.Empty)
  have productManifold : ManifoldSingletonCarrier product :=
    productEmpty
  have inverseEmpty : hsame (GroupSingletonInv h) BHist.Empty := by
    rfl
  have inverseManifold : ManifoldSingletonCarrier (GroupSingletonInv h) :=
    inverseEmpty
  have chartRows :=
    ManifoldSingleton_chart_coverage productManifold domainReadback valueReadback
  exact And.intro productEmpty
    (And.intro productManifold
      (And.intro inverseEmpty
        (And.intro inverseManifold
          (And.intro chartRows.left
            (And.intro chartRows.right.right.left chartRows.right.right.right)))))

end BEDC.Derived.LieGroupUp
