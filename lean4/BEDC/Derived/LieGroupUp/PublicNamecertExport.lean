import BEDC.Derived.LieGroupUp

namespace BEDC.Derived.LieGroupUp

open BEDC.Derived.ManifoldUp
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem LieGroupSingleton_public_namecert_export :
    SemanticNameCert LieGroupSingletonCarrier LieGroupSingletonCarrier
        LieGroupSingletonCarrier LieGroupSingletonClassifier ∧
      (forall {h k product mulChart invChart : BHist}, LieGroupSingletonCarrier h ->
        LieGroupSingletonCarrier k -> Cont h k product -> Cont BHist.Empty product mulChart ->
          Cont BHist.Empty (LieGroupSingletonInv h) invChart ->
            LieGroupSingletonClassifier product BHist.Empty ∧ ManifoldSingletonCarrier product ∧
              hsame mulChart BHist.Empty ∧ hsame invChart BHist.Empty ∧
                UnaryHistory mulChart ∧ UnaryHistory invChart) := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory SemanticNameCert
  exact And.intro LieGroupSingleton_carrier_obligation.left
    (fun carrierH carrierK productRow mulChartRow invChartRow =>
      LieGroupSingleton_chart_operation_readback carrierH carrierK productRow mulChartRow
        invChartRow)

end BEDC.Derived.LieGroupUp
