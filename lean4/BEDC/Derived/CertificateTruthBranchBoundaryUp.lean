import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CertificateTruthBranchBoundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
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

end BEDC.Derived.CertificateTruthBranchBoundaryUp
