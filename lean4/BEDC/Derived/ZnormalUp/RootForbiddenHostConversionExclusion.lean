import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalPacket_root_forbidden_host_conversion_exclusion [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name refusalAudit :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont provenance name refusalAudit →
        PkgSig bundle refusalAudit pkg →
          SemanticNameCert
              (fun row : BHist => hsame row refusalAudit ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row provenance ∨ hsame row name ∨ hsame row refusalAudit)
              (fun row : BHist =>
                hsame row refusalAudit ∧ PkgSig bundle refusalAudit pkg)
              hsame ∧
            UnaryHistory refusalAudit ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle refusalAudit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet provenanceNameRefusalAudit refusalAuditPkg
  obtain ⟨_typedUnary, _fuelUnary, _terminalUnary, _normalUnary, _continuationUnary,
    _transportsUnary, _routesUnary, provenanceUnary, nameUnary, _typedFuelTerminal,
    _terminalNormalContinuation, _continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have refusalAuditUnary : UnaryHistory refusalAudit :=
    unary_cont_closed provenanceUnary nameUnary provenanceNameRefusalAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalAudit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row provenance ∨ hsame row name ∨ hsame row refusalAudit)
          (fun row : BHist => hsame row refusalAudit ∧ PkgSig bundle refusalAudit pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro refusalAudit ⟨hsame_refl refusalAudit, refusalAuditUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, refusalAuditPkg⟩
  }
  exact ⟨cert, refusalAuditUnary, provenancePkg, refusalAuditPkg⟩

end BEDC.Derived.ZnormalUp
