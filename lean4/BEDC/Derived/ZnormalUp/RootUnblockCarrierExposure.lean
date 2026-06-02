import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_unblock_carrier_exposure [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont typed fuel terminal →
        Cont terminal normal continuation →
          Cont continuation transports routes →
            Cont routes name auditRead →
              PkgSig bundle auditRead pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                        hsame row normal ∨ hsame row continuation ∨
                          hsame row transports ∨ hsame row routes ∨
                            hsame row provenance ∨ hsame row name ∨ hsame row auditRead)
                    (fun row : BHist =>
                      hsame row auditRead ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle name pkg ∧ PkgSig bundle auditRead pkg)
                    hsame ∧
                  UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
                    UnaryHistory normal ∧ UnaryHistory continuation ∧
                      UnaryHistory transports ∧ UnaryHistory routes ∧
                        UnaryHistory auditRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle PkgSig SemanticNameCert UnaryHistory
  intro packet typedFuelTerminal _terminalNormalContinuation
    _continuationTransportsRoutes routesNameAudit auditPkg
  obtain ⟨typedUnary, fuelUnary, _terminalUnary, normalUnary, _continuationUnary,
    transportsUnary, _routesUnary, _provenanceUnary, nameUnary, _packetTypedFuelTerminal,
    packetTerminalNormalContinuation, packetContinuationTransportsRoutes, namePkg,
    provenancePkg⟩ := packet
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed typedUnary fuelUnary typedFuelTerminal
  have continuationUnary : UnaryHistory continuation :=
    unary_cont_closed terminalUnary normalUnary packetTerminalNormalContinuation
  have routesUnary : UnaryHistory routes :=
    unary_cont_closed continuationUnary transportsUnary packetContinuationTransportsRoutes
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed routesUnary nameUnary routesNameAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row auditRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨ hsame row normal ∨
              hsame row continuation ∨ hsame row transports ∨ hsame row routes ∨
                hsame row provenance ∨ hsame row name ∨ hsame row auditRead)
          (fun row : BHist =>
            hsame row auditRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle name pkg ∧ PkgSig bundle auditRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro auditRead ⟨hsame_refl auditRead, auditUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, provenancePkg, namePkg, auditPkg⟩
  }
  exact
    ⟨cert, typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, auditUnary⟩

end BEDC.Derived.ZnormalUp
