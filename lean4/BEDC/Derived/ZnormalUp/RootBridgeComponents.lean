import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootTotalHostBridgeComponents [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name hostRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal hostRead →
        PkgSig bundle hostRead pkg →
          hsame hostRead continuation ∧ UnaryHistory hostRead ∧ Cont typed fuel terminal ∧
            Cont terminal normal continuation ∧ Cont terminal normal hostRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle hostRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame UnaryHistory
  intro packet terminalNormalHostRead hostReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, typedFuelTerminal,
    terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have hostReadSame : hsame hostRead continuation :=
    cont_deterministic terminalNormalHostRead terminalNormalContinuation
  have hostReadUnary : UnaryHistory hostRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalHostRead
  exact
    ⟨hostReadSame, hostReadUnary, typedFuelTerminal, terminalNormalContinuation,
      terminalNormalHostRead, provenancePkg, hostReadPkg⟩

end BEDC.Derived.ZnormalUp
