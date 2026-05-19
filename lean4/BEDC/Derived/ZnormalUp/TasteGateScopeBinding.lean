import BEDC.Derived.ZnormalUp.TasteGate

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_tastegate_scope_binding [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name fieldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont terminal normal fieldRead →
        PkgSig bundle fieldRead pkg →
          zNormalFields
              (ZNormalUp.mk typed fuel terminal normal continuation transports routes provenance
                name) =
            [typed, fuel, terminal, normal, continuation, transports, routes, provenance,
              name] ∧
            UnaryHistory terminal ∧ UnaryHistory normal ∧ UnaryHistory fieldRead ∧
              Cont terminal normal fieldRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle fieldRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg FieldFaithful UnaryHistory PkgSig
  intro packet terminalNormalFieldRead fieldReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have fieldReadUnary : UnaryHistory fieldRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalFieldRead
  exact
    ⟨rfl, terminalUnary, normalUnary, fieldReadUnary, terminalNormalFieldRead,
      provenancePkg, fieldReadPkg⟩

end BEDC.Derived.ZnormalUp
