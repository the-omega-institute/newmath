import BEDC.Derived.FiniteNetMinimumFoldUp

namespace BEDC.Derived.FiniteNetMinimumFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteNetMinimumFoldPacket_compact_uniform_pointwise_radius_chain
    [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow compactInput folded
      lowerExport handoff finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont bundleRow radius compactInput →
        Cont compactInput accumulator folded →
          Cont folded lower lowerExport →
            Cont accumulator lower handoff →
              hsame handoff transport →
                Cont lowerExport handoff finalRead →
                  PkgSig bundle lowerExport pkg →
                    PkgSig bundle handoff pkg →
                      UnaryHistory compactInput ∧ UnaryHistory folded ∧
                        UnaryHistory lowerExport ∧ UnaryHistory handoff ∧
                          UnaryHistory finalRead ∧ Cont bundleRow radius compactInput ∧
                            Cont compactInput accumulator folded ∧ Cont folded lower lowerExport ∧
                              Cont accumulator lower handoff ∧ hsame handoff transport ∧
                                Cont lowerExport handoff finalRead ∧
                                  PkgSig bundle lowerExport pkg ∧
                                    PkgSig bundle handoff pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame ProbeBundle Pkg
  intro packet bundleRadiusCompact compactAccumulatorFolded foldedLowerExport
    accumulatorLowerHandoff handoffSame lowerExportHandoffFinal lowerExportPkg handoffPkg
  obtain ⟨bundleRowUnary, radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, _transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _packetPkg⟩ := packet
  have compactInputUnary : UnaryHistory compactInput :=
    unary_cont_closed bundleRowUnary radiusUnary bundleRadiusCompact
  have foldedUnary : UnaryHistory folded :=
    unary_cont_closed compactInputUnary accumulatorUnary compactAccumulatorFolded
  have lowerExportUnary : UnaryHistory lowerExport :=
    unary_cont_closed foldedUnary lowerUnary foldedLowerExport
  have handoffUnary : UnaryHistory handoff :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerHandoff
  have finalReadUnary : UnaryHistory finalRead :=
    unary_cont_closed lowerExportUnary handoffUnary lowerExportHandoffFinal
  exact
    ⟨compactInputUnary, foldedUnary, lowerExportUnary, handoffUnary, finalReadUnary,
      bundleRadiusCompact, compactAccumulatorFolded, foldedLowerExport,
      accumulatorLowerHandoff, handoffSame, lowerExportHandoffFinal, lowerExportPkg,
      handoffPkg⟩

end BEDC.Derived.FiniteNetMinimumFoldUp
