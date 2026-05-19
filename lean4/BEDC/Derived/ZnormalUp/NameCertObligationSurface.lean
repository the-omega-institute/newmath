import BEDC.Derived.ZnormalUp

namespace BEDC.Derived.ZnormalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZnormalNameCertObligationSurface [AskSetup] [PackageSetup]
    {typed fuel terminal normal continuation transports routes provenance name audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZnormalPacket typed fuel terminal normal continuation transports routes provenance name
        bundle pkg →
      Cont routes name audit →
        PkgSig bundle audit pkg →
          SemanticNameCert
              (fun row : BHist => hsame row audit ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
                  hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                    hsame row routes ∨ hsame row audit)
              (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
              hsame ∧
            UnaryHistory typed ∧ UnaryHistory fuel ∧ UnaryHistory terminal ∧
              UnaryHistory normal ∧ UnaryHistory continuation ∧ UnaryHistory transports ∧
                UnaryHistory routes ∧ UnaryHistory audit ∧ Cont typed fuel terminal ∧
                  Cont terminal normal continuation ∧ Cont continuation transports routes ∧
                    Cont routes name audit ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro packet routesNameAudit auditPkg
  obtain ⟨typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
    transportsUnary, routesUnary, _provenanceUnary, nameUnary, typedFuelTerminal,
    terminalNormalContinuation, continuationTransportsRoutes, _namePkg, provenancePkg⟩ :=
    packet
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed routesUnary nameUnary routesNameAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row audit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row typed ∨ hsame row fuel ∨ hsame row terminal ∨
              hsame row normal ∨ hsame row continuation ∨ hsame row transports ∨
                hsame row routes ∨ hsame row audit)
          (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro audit ⟨hsame_refl audit, auditUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other sameRows
          exact hsame_symm sameRows
        equiv_trans := by
          intro _row _middle _other sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro _row _other sameRows source
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
                      (Or.inr source.left))))))
      ledger_sound := by
        intro _row source
        exact ⟨source.left, auditPkg⟩
    }
  exact
    ⟨cert, typedUnary, fuelUnary, terminalUnary, normalUnary, continuationUnary,
      transportsUnary, routesUnary, auditUnary, typedFuelTerminal,
      terminalNormalContinuation, continuationTransportsRoutes, routesNameAudit,
      provenancePkg, auditPkg⟩

end BEDC.Derived.ZnormalUp
