import BEDC.Derived.FiniteNetMinimumFoldUp

namespace BEDC.Derived.FiniteNetMinimumFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteNetMinimumFoldPacket_terminal_readback [AskSetup] [PackageSetup]
    {bundleRow radius accumulator lower transport route provenance nameRow lowerExport
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FiniteNetMinimumFoldPacket bundleRow radius accumulator lower transport route provenance
        nameRow bundle pkg →
      Cont accumulator lower lowerExport →
        hsame terminalRead lowerExport →
          PkgSig bundle lowerExport pkg →
            PkgSig bundle terminalRead pkg →
              UnaryHistory accumulator ∧ UnaryHistory lower ∧ UnaryHistory lowerExport ∧
                UnaryHistory terminalRead ∧ Cont accumulator lower lowerExport ∧
                  hsame terminalRead lowerExport ∧ Cont transport nameRow provenance ∧
                    PkgSig bundle lowerExport pkg ∧ PkgSig bundle terminalRead pkg := by
  -- BEDC touchpoint anchor: BHist UnaryHistory hsame Cont ProbeBundle Pkg
  intro packet accumulatorLowerExport terminalSame lowerExportPkg terminalPkg
  obtain ⟨_bundleRowUnary, _radiusUnary, accumulatorUnary, lowerUnary, _nameRowUnary,
    _bundleRadiusAccumulator, _accumulatorLowerTransport, transportNameProvenance,
    _bundleRadiusTransport, _transportAccumulatorLower, _lowerRouteProvenance,
    _provenancePkg⟩ := packet
  have lowerExportUnary : UnaryHistory lowerExport :=
    unary_cont_closed accumulatorUnary lowerUnary accumulatorLowerExport
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_transport_symm lowerExportUnary terminalSame
  exact
    ⟨accumulatorUnary, lowerUnary, lowerExportUnary, terminalReadUnary,
      accumulatorLowerExport, terminalSame, transportNameProvenance, lowerExportPkg,
      terminalPkg⟩

end BEDC.Derived.FiniteNetMinimumFoldUp
