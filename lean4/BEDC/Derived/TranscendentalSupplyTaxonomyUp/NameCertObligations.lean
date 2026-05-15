import BEDC.Derived.TranscendentalSupplyTaxonomyUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.TranscendentalSupplyTaxonomyUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

theorem TranscendentalSupplyTaxonomyNameCert_obligations
    {socketKind requestedSupply gap auditGate site transport route provenance name : BHist}
    (siteGapRoute : Cont site gap route) (gapAuditRoute : Cont gap auditGate route) :
    SemanticNameCert
      (fun row : BHist =>
        hsame row socketKind ∧
          ∃ packet : TranscendentalSupplyTaxonomyUp,
            packet =
              TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
                transport route provenance name)
      (fun row : BHist =>
        hsame row socketKind ∧ hsame requestedSupply requestedSupply ∧ hsame gap gap ∧
          hsame auditGate auditGate ∧ hsame site site)
      (fun row : BHist =>
        hsame row socketKind ∧ Cont site gap route ∧ Cont gap auditGate route ∧
          hsame transport transport ∧ hsame provenance provenance ∧ hsame name name)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  have sourceSocket :
      (fun row : BHist =>
        hsame row socketKind ∧
          ∃ packet : TranscendentalSupplyTaxonomyUp,
            packet =
              TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
                transport route provenance name) socketKind := by
    exact
      ⟨hsame_refl socketKind,
        Exists.intro
          (TranscendentalSupplyTaxonomyUp.mk socketKind requestedSupply gap auditGate site
            transport route provenance name)
          rfl⟩
  exact {
    core := {
      carrier_inhabited := Exists.intro socketKind sourceSocket
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' same
        exact hsame_symm same
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' same source
        exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact
        ⟨source.left, hsame_refl requestedSupply, hsame_refl gap, hsame_refl auditGate,
          hsame_refl site⟩
    ledger_sound := by
      intro _row source
      exact
        ⟨source.left, siteGapRoute, gapAuditRoute, hsame_refl transport,
          hsame_refl provenance, hsame_refl name⟩
  }

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def TranscendentalSupplyTaxonomyCarrier [AskSetup] [PackageSetup]
    (socketKind requestedSupply gap auditGate site transport route provenance nameRow :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory socketKind ∧ UnaryHistory requestedSupply ∧ UnaryHistory gap ∧
    UnaryHistory auditGate ∧ UnaryHistory site ∧ UnaryHistory transport ∧
      UnaryHistory route ∧ UnaryHistory provenance ∧ UnaryHistory nameRow ∧
        Cont socketKind requestedSupply gap ∧ Cont gap auditGate site ∧
          Cont site transport route ∧ Cont route provenance nameRow ∧
            hsame site (append gap auditGate) ∧ PkgSig bundle provenance pkg

theorem TranscendentalSupplyTaxonomyCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {socketKind requestedSupply gap auditGate site transport route provenance nameRow auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TranscendentalSupplyTaxonomyCarrier socketKind requestedSupply gap auditGate site transport
        route provenance nameRow bundle pkg →
      Cont gap auditGate auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                TranscendentalSupplyTaxonomyCarrier socketKind requestedSupply gap auditGate
                  site transport route provenance nameRow bundle pkg ∧ hsame row auditGate)
              (fun row : BHist => hsame row auditGate ∧ UnaryHistory row)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                  Cont gap auditGate auditRead)
              hsame ∧
            UnaryHistory socketKind ∧ UnaryHistory requestedSupply ∧ UnaryHistory gap ∧
              UnaryHistory auditGate ∧ UnaryHistory auditRead ∧
                Cont socketKind requestedSupply gap ∧ Cont gap auditGate auditRead ∧
                  PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier gapAuditRead auditPkg
  have carrierPacket :
      TranscendentalSupplyTaxonomyCarrier socketKind requestedSupply gap auditGate site
        transport route provenance nameRow bundle pkg :=
    carrier
  obtain ⟨socketKindUnary, requestedSupplyUnary, gapUnary, auditGateUnary, _siteUnary,
    _transportUnary, _routeUnary, _provenanceUnary, _nameRowUnary,
    socketRequestedGap, _gapAuditSite, _siteTransportRoute, _routeProvenanceName,
    _siteSameGapAudit, provenancePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed gapUnary auditGateUnary gapAuditRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            TranscendentalSupplyTaxonomyCarrier socketKind requestedSupply gap auditGate
              site transport route provenance nameRow bundle pkg ∧ hsame row auditGate)
          (fun row : BHist => hsame row auditGate ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
              Cont gap auditGate auditRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro auditGate ⟨carrierPacket, hsame_refl auditGate⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right, unary_transport auditGateUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, auditPkg, gapAuditRead⟩
    }
  exact
    ⟨cert, socketKindUnary, requestedSupplyUnary, gapUnary, auditGateUnary,
      auditReadUnary, socketRequestedGap, gapAuditRead, auditPkg⟩

end BEDC.Derived.TranscendentalSupplyTaxonomyUp
