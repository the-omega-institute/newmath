import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalRootFiniteFuelAdmissionCertificate [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name fuelRead
      terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg ->
      Cont typed fuel fuelRead ->
        Cont fuelRead terminal terminalRead ->
          PkgSig bundle terminalRead pkg ->
            SemanticNameCert
                (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  Cont typed fuel fuelRead ∧ Cont fuelRead terminal row ∧
                    PkgSig bundle terminalRead pkg)
                (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRead pkg)
                hsame ∧
              UnaryHistory fuelRead ∧ UnaryHistory terminalRead ∧
                PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet typedFuelRead fuelReadTerminalRead terminalReadPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, _provenanceUnary, _nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have fuelReadUnary : UnaryHistory fuelRead :=
    unary_cont_closed typedUnary fuelUnary typedFuelRead
  have terminalReadUnary : UnaryHistory terminalRead :=
    unary_cont_closed fuelReadUnary terminalUnary fuelReadTerminalRead
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont typed fuel fuelRead ∧ Cont fuelRead terminal row ∧
              PkgSig bundle terminalRead pkg)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle terminalRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead
        ⟨hsame_refl terminalRead, terminalReadUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨typedFuelRead,
          cont_result_hsame_transport fuelReadTerminalRead (hsame_symm source.left),
          terminalReadPkg⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.right, terminalReadPkg⟩
  }
  exact ⟨cert, fuelReadUnary, terminalReadUnary, provenancePkg⟩

end BEDC.Derived.ZnormalUp
