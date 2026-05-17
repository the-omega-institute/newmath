import BEDC.Derived.FiniteNetMinimumFoldUp

namespace BEDC.Derived.FiniteNetMinimumFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteNetMinimumFoldPacket_uniformmodulus_compactmetric_handoff_gate
    [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow uniformRead
      compactRead terminal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont accumulator lower uniformRead →
        Cont bundleRow radius compactRead →
          Cont compactRead uniformRead terminal →
            PkgSig bundle uniformRead pkg →
              PkgSig bundle terminal pkg →
                UnaryHistory bundleRow ∧ UnaryHistory radius ∧ UnaryHistory accumulator ∧
                  UnaryHistory lower ∧ UnaryHistory uniformRead ∧
                    UnaryHistory compactRead ∧ UnaryHistory terminal ∧
                      Cont bundleRow radius compactRead ∧
                        Cont accumulator lower uniformRead ∧
                          Cont compactRead uniformRead terminal ∧
                            Cont transport nameRow provenance ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle uniformRead pkg ∧
                                  PkgSig bundle terminal pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle Pkg
  intro packet accumulatorLowerUniform bundleRadiusCompact compactUniformTerminal
    uniformPkg terminalPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    provenancePkg⟩ := packet
  have uniformReadUnary : UnaryHistory uniformRead :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerUniform
  have compactReadUnary : UnaryHistory compactRead :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCompact
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed compactReadUnary uniformReadUnary compactUniformTerminal
  exact
    ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, uniformReadUnary,
      compactReadUnary, terminalUnary, bundleRadiusCompact, accumulatorLowerUniform,
      compactUniformTerminal, transportNameProvenance, provenancePkg, uniformPkg,
      terminalPkg⟩

end BEDC.Derived.FiniteNetMinimumFoldUp
