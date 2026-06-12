import BEDC.Derived.CoveringdimensionUp

namespace BEDC.Derived.CoveringdimensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CoveringDimensionRootCoverCarrierPacket [AskSetup] [PackageSetup]
    (compactMetric epsilonNet cover refinement orderBound density nerve transport replay
      provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
    UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory density ∧
      UnaryHistory nerve ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧ Cont compactMetric epsilonNet cover ∧
          Cont cover refinement orderBound ∧ Cont density nerve replay ∧
            Cont transport replay provenance ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle localName pkg

theorem CoveringDimensionRootCoverCarrierPacket_finite_route [AskSetup] [PackageSetup]
    {compactMetric epsilonNet cover refinement orderBound density nerve transport replay
      provenance localName densityRead nerveRead rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringDimensionRootCoverCarrierPacket compactMetric epsilonNet cover refinement orderBound
        density nerve transport replay provenance localName bundle pkg →
      Cont orderBound density densityRead →
        Cont densityRead nerve nerveRead →
          Cont cover nerveRead rootRead →
            UnaryHistory compactMetric ∧ UnaryHistory epsilonNet ∧ UnaryHistory cover ∧
              UnaryHistory refinement ∧ UnaryHistory orderBound ∧ UnaryHistory density ∧
                UnaryHistory nerve ∧ UnaryHistory densityRead ∧ UnaryHistory nerveRead ∧
                  UnaryHistory rootRead ∧ Cont compactMetric epsilonNet cover ∧
                    Cont cover refinement orderBound ∧ Cont orderBound density densityRead ∧
                      Cont densityRead nerve nerveRead ∧ Cont cover nerveRead rootRead ∧
                        Cont density nerve replay ∧ Cont transport replay provenance ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro packet densityRoute nerveRoute rootRoute
  obtain ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, densityUnary,
    nerveUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    compactEpsilonCover, coverRefinementOrder, densityNerveReplay,
    transportReplayProvenance, provenancePkg, localNamePkg⟩ := packet
  have densityReadUnary : UnaryHistory densityRead :=
    unary_cont_closed orderUnary densityUnary densityRoute
  have nerveReadUnary : UnaryHistory nerveRead :=
    unary_cont_closed densityReadUnary nerveUnary nerveRoute
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed coverUnary nerveReadUnary rootRoute
  exact
    ⟨compactUnary, epsilonUnary, coverUnary, refinementUnary, orderUnary, densityUnary,
      nerveUnary, densityReadUnary, nerveReadUnary, rootReadUnary, compactEpsilonCover,
      coverRefinementOrder, densityRoute, nerveRoute, rootRoute, densityNerveReplay,
      transportReplayProvenance, provenancePkg, localNamePkg⟩

end BEDC.Derived.CoveringdimensionUp
