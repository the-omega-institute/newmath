import BEDC.Derived.ApophaticNameUp

namespace BEDC.Derived.ApophaticNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticNameCarrier_public_boundary_package [AskSetup] [PackageSetup]
    {socket request gate ledger transport route provenance nameRow publicRead auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg →
      Cont route provenance publicRead →
        Cont publicRead nameRow auditRead →
          PkgSig bundle publicRead pkg →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticNameCarrier socket request gate ledger transport route provenance
                      nameRow bundle pkg ∧ hsame row publicRead)
                  (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
                      PkgSig bundle auditRead pkg)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory request ∧ UnaryHistory gate ∧
                UnaryHistory ledger ∧ UnaryHistory publicRead ∧ UnaryHistory auditRead ∧
                Cont socket request gate ∧ Cont gate ledger route ∧
                Cont route provenance publicRead ∧ Cont publicRead nameRow auditRead ∧
                hsame ledger (append request gate) ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle publicRead pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier routeProvenancePublic publicNameAudit publicPkg auditPkg
  have carrierPacket :
      ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
        bundle pkg :=
    carrier
  obtain ⟨socketUnary, requestUnary, gateUnary, ledgerUnary, _transportUnary, routeUnary,
    provenanceUnary, nameRowUnary, socketRequestGate, _requestGateRoute, gateLedgerRoute,
    _gateLedgerNameRow, ledgerSameRequestGate, provenancePkg⟩ := carrier
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenancePublic
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed publicUnary nameRowUnary publicNameAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticNameCarrier socket request gate ledger transport route provenance nameRow
              bundle pkg ∧ hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle publicRead pkg ∧
              PkgSig bundle auditRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro publicRead ⟨carrierPacket, hsame_refl publicRead⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      have rowSamePublic : hsame row publicRead := source.right
      exact ⟨rowSamePublic, unary_transport publicUnary (hsame_symm rowSamePublic)⟩
    · intro _row _source
      exact ⟨provenancePkg, publicPkg, auditPkg⟩
  exact
    ⟨cert, socketUnary, requestUnary, gateUnary, ledgerUnary, publicUnary, auditUnary,
      socketRequestGate, gateLedgerRoute, routeProvenancePublic, publicNameAudit,
      ledgerSameRequestGate, provenancePkg, publicPkg, auditPkg⟩

end BEDC.Derived.ApophaticNameUp
