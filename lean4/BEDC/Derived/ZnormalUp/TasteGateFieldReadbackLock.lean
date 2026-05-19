import BEDC.Derived.ZnormalUp.TasteGate

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Meta.TasteGate

theorem ZnormalTasteGateFieldReadbackLock [AskSetup] [PackageSetup]
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
            (∃ x y : ZNormalUp, x ≠ y) ∧ UnaryHistory terminal ∧ UnaryHistory normal ∧
              UnaryHistory fieldRead ∧ Cont terminal normal fieldRead ∧
                PkgSig bundle provenance pkg ∧ PkgSig bundle fieldRead pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg FieldFaithful Nontrivial UnaryHistory
  intro packet terminalNormalFieldRead fieldReadPkg
  obtain ⟨_typedUnary, _fuelUnary, terminalUnary, normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have fieldReadUnary : UnaryHistory fieldRead :=
    unary_cont_closed terminalUnary normalUnary terminalNormalFieldRead
  have fieldsReadback :
      zNormalFields
          (ZNormalUp.mk typed fuel terminal normal continuation transports routes provenance
            name) =
        [typed, fuel, terminal, normal, continuation, transports, routes, provenance,
          name] := by
    rfl
  have witnessPair : ∃ x y : ZNormalUp, x ≠ y := by
    exact
      Exists.intro
        (ZNormalUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
        (Exists.intro
          (ZNormalUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
          (by
            intro h
            cases h))
  exact
    ⟨fieldsReadback, witnessPair, terminalUnary, normalUnary,
      fieldReadUnary, terminalNormalFieldRead, provenancePkg, fieldReadPkg⟩

end BEDC.Derived.ZnormalUp
