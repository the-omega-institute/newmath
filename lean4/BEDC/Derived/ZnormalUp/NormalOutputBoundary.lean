import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_normal_output_boundary [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name outputRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal continuation outputRead →
        PkgSig bundle outputRead pkg →
          UnaryHistory terminal ∧ UnaryHistory continuation ∧ UnaryHistory outputRead ∧
            Cont typed fuel terminal ∧ Cont terminal normal continuation ∧
              Cont terminal continuation outputRead ∧ PkgSig bundle name pkg ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle outputRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro packet terminalContinuationOutput outputReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, _normalUnary, continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, namePkg, provenancePkg⟩ :=
    packet
  have outputReadUnary : UnaryHistory outputRead :=
    unary_cont_closed terminalUnary continuationUnary terminalContinuationOutput
  exact
    ⟨terminalUnary, continuationUnary, outputReadUnary, typedFuelTerminal,
      terminalNormalContinuation, terminalContinuationOutput, namePkg, provenancePkg,
      outputReadPkg⟩

end BEDC.Derived.ZnormalUp
