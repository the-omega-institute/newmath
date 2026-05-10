import BEDC.Derived.ManifoldUp

namespace BEDC.Derived.ManifoldUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem ManifoldUp_StdBridge :
    SemanticNameCert ManifoldSingletonCarrier ManifoldSingletonCarrier ManifoldSingletonCarrier
        (fun h k : BHist =>
          ManifoldSingletonCarrier h ∧ ManifoldSingletonCarrier k ∧ hsame h k) ∧
      (forall {h domain value : BHist}, ManifoldSingletonCarrier h ->
        Cont BHist.Empty h domain -> Cont h BHist.Empty value ->
          hsame domain BHist.Empty ∧ hsame value h ∧ hsame value BHist.Empty ∧
            UnaryHistory value) ∧
      (forall {h : BHist}, ManifoldSingletonCarrier h ->
        UnaryHistory h ∧ Cont BHist.Empty h h) := by
  constructor
  · exact ManifoldSingleton_semanticNameCert.left
  · constructor
    · intro h domain value carrier domainReadback valueReadback
      exact ManifoldSingleton_chart_coverage carrier domainReadback valueReadback
    · intro h carrier
      exact ManifoldSingletonCarrier_topology_scope carrier |>.right

end BEDC.Derived.ManifoldUp
