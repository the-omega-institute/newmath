import BEDC.Derived.WeylGroupUp

namespace BEDC.Derived.WeylGroupUp

open BEDC.Derived.GroupUp
open BEDC.Derived.RootSystemUp
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem WeylGroupRootSystem_mature_bridge_consumption {support : ProbeBundle BHist}
    {Vector Nonzero : BHist -> Prop}
    (vector_unary : forall {h : BHist}, Vector h -> UnaryHistory h)
    {root word action next actionNext braid : BHist} :
    WeylGroupBHistSourceRow support Vector Nonzero root word action ->
      GroupSingletonCarrier next ->
        Cont action next actionNext ->
          Cont word next braid ->
            RootSystemFiniteSupportCarrier support Vector Nonzero root ∧
              WeylGroupBHistSourceRow support Vector Nonzero root braid actionNext ∧
                SemanticNameCert
                  (fun endpoint : BHist =>
                    WeylGroupBHistSourceRow support Vector Nonzero root braid endpoint ∧
                      hsame endpoint actionNext)
                  (fun endpoint : BHist =>
                    WeylGroupBHistSourceRow support Vector Nonzero root braid endpoint ∧
                      hsame endpoint actionNext)
                  (fun endpoint : BHist =>
                    WeylGroupBHistSourceRow support Vector Nonzero root braid endpoint ∧
                      hsame endpoint actionNext)
                  hsame := by
  intro source nextCarrier actionStep braidStep
  have exported :
      WeylGroupBHistSourceRow support Vector Nonzero root braid actionNext ∧
        hsame actionNext root ∧ GroupSingletonClassifier braid BHist.Empty :=
    WeylGroupPublicNameCert_export vector_unary source nextCarrier actionStep braidStep
  exact And.intro source.left
    (And.intro exported.left
      (WeylGroupStandardReflectionGroup_bridge vector_unary source nextCarrier actionStep
        braidStep))

end BEDC.Derived.WeylGroupUp
