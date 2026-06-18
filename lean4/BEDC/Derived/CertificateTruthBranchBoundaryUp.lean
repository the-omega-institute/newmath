import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertificateTruthBranchBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CertificateTruthBranchBoundaryCarrier [AskSetup] [PackageSetup]
    (query assumption refutation decision refusal ledger transport continuation provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  UnaryHistory query ∧ UnaryHistory assumption ∧ UnaryHistory refutation ∧
    UnaryHistory decision ∧ UnaryHistory refusal ∧ UnaryHistory ledger ∧
      UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ Cont query assumption refutation ∧ Cont decision refusal ledger ∧
          Cont transport continuation provenance ∧ PkgSig bundle localName pkg

theorem CertificateTruthBranchBoundaryNonescape [AskSetup] [PackageSetup]
    {query assumption refutation decision refusal ledger transport continuation provenance
      localName consumerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateTruthBranchBoundaryCarrier query assumption refutation decision refusal ledger
        transport continuation provenance localName bundle pkg →
      Cont refusal ledger consumerRead →
        PkgSig bundle consumerRead pkg →
          UnaryHistory query ∧ UnaryHistory assumption ∧ UnaryHistory refutation ∧
            UnaryHistory refusal ∧ UnaryHistory ledger ∧ UnaryHistory consumerRead ∧
              Cont query assumption refutation ∧ Cont refusal ledger consumerRead ∧
                PkgSig bundle localName pkg ∧ PkgSig bundle consumerRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier refusalLedger consumerPkg
  obtain ⟨queryUnary, assumptionUnary, refutationUnary, _decisionUnary, refusalUnary,
    ledgerUnary, _transportUnary, _continuationUnary, _provenanceUnary, _localNameUnary,
    queryAssumptionRefutation, _decisionRefusalLedger, _transportContinuationProvenance,
    localNamePkg⟩ := carrier
  have consumerUnary : UnaryHistory consumerRead :=
    unary_cont_closed refusalUnary ledgerUnary refusalLedger
  exact
    ⟨queryUnary, assumptionUnary, refutationUnary, refusalUnary, ledgerUnary, consumerUnary,
      queryAssumptionRefutation, refusalLedger, localNamePkg, consumerPkg⟩

theorem CertificateTruthBranchBoundaryNameCertObligations [AskSetup] [PackageSetup]
    {query assumption refutation decision refusal ledger transport continuation provenance
      localName decisionRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateTruthBranchBoundaryCarrier query assumption refutation decision refusal ledger
        transport continuation provenance localName bundle pkg ->
      Cont decision refusal decisionRead ->
        Cont transport continuation transportRead ->
          PkgSig bundle decisionRead pkg ->
            PkgSig bundle transportRead pkg ->
              UnaryHistory query ∧ UnaryHistory assumption ∧ UnaryHistory refutation ∧
                UnaryHistory decision ∧ UnaryHistory refusal ∧ UnaryHistory ledger ∧
                  UnaryHistory transport ∧ UnaryHistory continuation ∧ UnaryHistory provenance ∧
                    UnaryHistory localName ∧ UnaryHistory decisionRead ∧
                      UnaryHistory transportRead ∧ Cont query assumption refutation ∧
                        Cont decision refusal ledger ∧ Cont transport continuation provenance ∧
                          Cont decision refusal decisionRead ∧
                            Cont transport continuation transportRead ∧
                              PkgSig bundle localName pkg ∧ PkgSig bundle decisionRead pkg ∧
                                PkgSig bundle transportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier decisionRefusalRead transportContinuationRead decisionReadPkg transportReadPkg
  obtain ⟨queryUnary, assumptionUnary, refutationUnary, decisionUnary, refusalUnary,
    ledgerUnary, transportUnary, continuationUnary, provenanceUnary, localNameUnary,
    queryAssumptionRefutation, decisionRefusalLedger, transportContinuationProvenance,
    localNamePkg⟩ := carrier
  have decisionReadUnary : UnaryHistory decisionRead :=
    unary_cont_closed decisionUnary refusalUnary decisionRefusalRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed transportUnary continuationUnary transportContinuationRead
  exact
    ⟨queryUnary, assumptionUnary, refutationUnary, decisionUnary, refusalUnary, ledgerUnary,
      transportUnary, continuationUnary, provenanceUnary, localNameUnary, decisionReadUnary,
      transportReadUnary, queryAssumptionRefutation, decisionRefusalLedger,
      transportContinuationProvenance, decisionRefusalRead, transportContinuationRead,
      localNamePkg, decisionReadPkg, transportReadPkg⟩

theorem CertificateTruthBranchBoundaryPublicInterface [AskSetup] [PackageSetup]
    {query assumption refutation decision refusal ledger transport continuation provenance
      localName publicRead decisionRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateTruthBranchBoundaryCarrier query assumption refutation decision refusal ledger
        transport continuation provenance localName bundle pkg ->
      Cont refusal ledger publicRead ->
        Cont decision refusal decisionRead ->
          Cont transport continuation transportRead ->
            PkgSig bundle publicRead pkg ->
              PkgSig bundle decisionRead pkg ->
                PkgSig bundle transportRead pkg ->
                  UnaryHistory query ∧ UnaryHistory assumption ∧ UnaryHistory refutation ∧
                    UnaryHistory decision ∧ UnaryHistory refusal ∧ UnaryHistory ledger ∧
                      UnaryHistory publicRead ∧ UnaryHistory decisionRead ∧
                        UnaryHistory transportRead ∧ Cont query assumption refutation ∧
                          Cont refusal ledger publicRead ∧ Cont decision refusal decisionRead ∧
                            Cont transport continuation transportRead ∧
                              PkgSig bundle localName pkg ∧ PkgSig bundle publicRead pkg ∧
                                PkgSig bundle decisionRead pkg ∧
                                  PkgSig bundle transportRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig
  intro carrier refusalLedgerPublic decisionRefusalRead transportContinuationRead publicReadPkg
    decisionReadPkg transportReadPkg
  obtain ⟨queryUnary, assumptionUnary, refutationUnary, decisionUnary, refusalUnary,
    ledgerUnary, transportUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    queryAssumptionRefutation, _decisionRefusalLedger, _transportContinuationProvenance,
    localNamePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed refusalUnary ledgerUnary refusalLedgerPublic
  have decisionReadUnary : UnaryHistory decisionRead :=
    unary_cont_closed decisionUnary refusalUnary decisionRefusalRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed transportUnary continuationUnary transportContinuationRead
  exact
    ⟨queryUnary, assumptionUnary, refutationUnary, decisionUnary, refusalUnary, ledgerUnary,
      publicReadUnary, decisionReadUnary, transportReadUnary, queryAssumptionRefutation,
      refusalLedgerPublic, decisionRefusalRead, transportContinuationRead, localNamePkg,
      publicReadPkg, decisionReadPkg, transportReadPkg⟩

theorem CertificateTruthBranchBoundaryBridgeInterface [AskSetup] [PackageSetup]
    {query assumption refutation decision refusal ledger transport continuation provenance
      localName bridgeRead decisionRead transportRead standardRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateTruthBranchBoundaryCarrier query assumption refutation decision refusal ledger
        transport continuation provenance localName bundle pkg →
      Cont refusal ledger bridgeRead →
        Cont decision refusal decisionRead →
          Cont transport continuation transportRead →
            Cont bridgeRead provenance standardRead →
              PkgSig bundle bridgeRead pkg →
                PkgSig bundle decisionRead pkg →
                  PkgSig bundle transportRead pkg →
                    PkgSig bundle standardRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row standardRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row query ∨ hsame row assumption ∨
                              hsame row refutation ∨ hsame row refusal ∨
                                hsame row ledger ∨ hsame row bridgeRead ∨
                                  hsame row standardRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont refusal ledger bridgeRead ∧
                              Cont bridgeRead provenance standardRead ∧
                                PkgSig bundle standardRead pkg)
                          hsame ∧
                        UnaryHistory bridgeRead ∧ UnaryHistory decisionRead ∧
                          UnaryHistory transportRead ∧ UnaryHistory standardRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier refusalLedgerBridge decisionRefusalRead transportContinuationRead
    bridgeProvenanceStandard _bridgeReadPkg _decisionReadPkg _transportReadPkg standardReadPkg
  obtain ⟨queryUnary, _assumptionUnary, _refutationUnary, decisionUnary, refusalUnary,
    ledgerUnary, transportUnary, continuationUnary, provenanceUnary, _localNameUnary,
    _queryAssumptionRefutation, _decisionRefusalLedger, _transportContinuationProvenance,
    _localNamePkg⟩ := carrier
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed refusalUnary ledgerUnary refusalLedgerBridge
  have decisionReadUnary : UnaryHistory decisionRead :=
    unary_cont_closed decisionUnary refusalUnary decisionRefusalRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed transportUnary continuationUnary transportContinuationRead
  have standardReadUnary : UnaryHistory standardRead :=
    unary_cont_closed bridgeReadUnary provenanceUnary bridgeProvenanceStandard
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row standardRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row query ∨ hsame row assumption ∨ hsame row refutation ∨
            hsame row refusal ∨ hsame row ledger ∨ hsame row bridgeRead ∨
              hsame row standardRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont refusal ledger bridgeRead ∧
            Cont bridgeRead provenance standardRead ∧ PkgSig bundle standardRead pkg)
        hsame := {
      core := {
        carrier_inhabited := Exists.intro standardRead
          ⟨hsame_refl standardRead, standardReadUnary⟩
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          exact
            ⟨hsame_trans (hsame_symm same) source.left,
              unary_transport source.right same⟩
      }
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
      ledger_sound := by
        intro row source
        exact
          ⟨source.right, refusalLedgerBridge, bridgeProvenanceStandard, standardReadPkg⟩
    }
  exact ⟨cert, bridgeReadUnary, decisionReadUnary, transportReadUnary, standardReadUnary⟩

theorem CertificateTruthBranchBoundaryBridgeReadInterface [AskSetup] [PackageSetup]
    {query assumption refutation decision refusal ledger transport continuation provenance
      localName bridgeRead publicRead decisionRead transportRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateTruthBranchBoundaryCarrier query assumption refutation decision refusal ledger
        transport continuation provenance localName bundle pkg ->
      Cont refusal ledger publicRead ->
        Cont publicRead localName bridgeRead ->
          Cont decision refusal decisionRead ->
            Cont transport continuation transportRead ->
              PkgSig bundle publicRead pkg ->
                PkgSig bundle bridgeRead pkg ->
                  PkgSig bundle decisionRead pkg ->
                    PkgSig bundle transportRead pkg ->
                      SemanticNameCert
                            (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row query ∨ hsame row assumption ∨
                                hsame row refutation ∨ hsame row decision ∨
                                  hsame row refusal ∨ hsame row ledger ∨
                                    hsame row publicRead ∨ hsame row bridgeRead)
                            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
                            hsame ∧
                          UnaryHistory bridgeRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert UnaryHistory Cont PkgSig
  intro carrier refusalLedgerPublic publicLocalBridge decisionRefusalRead
    _transportContinuationRead _publicReadPkg bridgeReadPkg _decisionReadPkg _transportReadPkg
  obtain ⟨_queryUnary, _assumptionUnary, _refutationUnary, decisionUnary, refusalUnary,
    ledgerUnary, _transportUnary, _continuationUnary, _provenanceUnary, localNameUnary,
    _queryAssumptionRefutation, _decisionRefusalLedger, _transportContinuationProvenance,
    localNamePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed refusalUnary ledgerUnary refusalLedgerPublic
  have bridgeReadUnary : UnaryHistory bridgeRead :=
    unary_cont_closed publicReadUnary localNameUnary publicLocalBridge
  have _decisionReadUnary : UnaryHistory decisionRead :=
    unary_cont_closed decisionUnary refusalUnary decisionRefusalRead
  have sourceAtBridge : hsame bridgeRead bridgeRead ∧ UnaryHistory bridgeRead :=
    ⟨hsame_refl bridgeRead, bridgeReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row bridgeRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row query ∨ hsame row assumption ∨ hsame row refutation ∨
              hsame row decision ∨ hsame row refusal ∨ hsame row ledger ∨
                hsame row publicRead ∨ hsame row bridgeRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle bridgeRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro bridgeRead sourceAtBridge
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, bridgeReadPkg⟩
  }
  exact ⟨cert, bridgeReadUnary, localNamePkg⟩

theorem CertificateTruthBranchBoundaryMaturePackage [AskSetup] [PackageSetup]
    {query assumption refutation decision refusal ledger transport continuation provenance
      localName publicRead decisionRead transportRead matureRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CertificateTruthBranchBoundaryCarrier query assumption refutation decision refusal ledger
        transport continuation provenance localName bundle pkg ->
      Cont refusal ledger publicRead ->
        Cont decision refusal decisionRead ->
          Cont transport continuation transportRead ->
            Cont publicRead transportRead matureRead ->
              PkgSig bundle publicRead pkg ->
                PkgSig bundle decisionRead pkg ->
                  PkgSig bundle transportRead pkg ->
                    PkgSig bundle matureRead pkg ->
                      SemanticNameCert
                            (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row publicRead ∨ hsame row decisionRead ∨
                                hsame row transportRead ∨ hsame row matureRead)
                            (fun row : BHist => UnaryHistory row ∧ PkgSig bundle matureRead pkg)
                            hsame ∧
                          UnaryHistory matureRead ∧ PkgSig bundle localName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert UnaryHistory Cont PkgSig
  intro carrier refusalLedgerPublic decisionRefusalRead transportContinuationRead publicTransportMature
    _publicReadPkg _decisionReadPkg _transportReadPkg matureReadPkg
  obtain ⟨_queryUnary, _assumptionUnary, _refutationUnary, decisionUnary, refusalUnary,
    ledgerUnary, transportUnary, continuationUnary, _provenanceUnary, _localNameUnary,
    _queryAssumptionRefutation, _decisionRefusalLedger, _transportContinuationProvenance,
    localNamePkg⟩ := carrier
  have publicReadUnary : UnaryHistory publicRead :=
    unary_cont_closed refusalUnary ledgerUnary refusalLedgerPublic
  have _decisionReadUnary : UnaryHistory decisionRead :=
    unary_cont_closed decisionUnary refusalUnary decisionRefusalRead
  have transportReadUnary : UnaryHistory transportRead :=
    unary_cont_closed transportUnary continuationUnary transportContinuationRead
  have matureReadUnary : UnaryHistory matureRead :=
    unary_cont_closed publicReadUnary transportReadUnary publicTransportMature
  have sourceAtMature : hsame matureRead matureRead ∧ UnaryHistory matureRead :=
    ⟨hsame_refl matureRead, matureReadUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row matureRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row publicRead ∨ hsame row decisionRead ∨ hsame row transportRead ∨
              hsame row matureRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle matureRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro matureRead sourceAtMature
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, matureReadPkg⟩
  }
  exact ⟨cert, matureReadUnary, localNamePkg⟩

end BEDC.Derived.CertificateTruthBranchBoundaryUp
