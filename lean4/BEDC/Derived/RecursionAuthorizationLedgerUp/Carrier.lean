import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RecursionAuthorizationLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RecursionAuthorizationLedgerCarrier [AskSetup] [PackageSetup]
    (signature recursor motive branches descent output transport routes provenance name : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  UnaryHistory signature ∧ UnaryHistory recursor ∧ UnaryHistory motive ∧
    UnaryHistory branches ∧ UnaryHistory descent ∧ UnaryHistory output ∧
      UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
        UnaryHistory name ∧ Cont signature recursor motive ∧ Cont branches descent output ∧
          Cont output transport routes ∧ Cont transport routes provenance ∧
            PkgSig bundle provenance pkg ∧ PkgSig bundle name pkg ∧
              SemanticNameCert
                (fun row : BHist => hsame row signature ∧ UnaryHistory row)
                (fun row : BHist => hsame row signature)
                (fun row : BHist => hsame row signature ∧ PkgSig bundle provenance pkg)
                hsame

theorem RecursionAuthorizationLedgerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {signature eliminator motive branch descent output transport route provenance name audit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature eliminator motive branch descent output
        transport route provenance name bundle pkg ->
      Cont signature eliminator motive ->
        Cont branch descent output ->
          Cont output route audit ->
            PkgSig bundle audit pkg ->
              SemanticNameCert
                  (fun row : BHist => hsame row audit ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
                      hsame row branch ∨ hsame row descent ∨ hsame row output ∨
                        hsame row audit)
                  (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
                  hsame ∧
                UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
                  UnaryHistory branch ∧ UnaryHistory descent ∧ UnaryHistory output ∧
                    UnaryHistory audit ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle audit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier signatureEliminatorMotive branchDescentOutput outputRouteAudit auditPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
    outputUnary, _transportUnary, routeUnary, provenanceUnary, nameUnary,
    _carrierSignatureEliminatorMotive, _carrierBranchDescentOutput,
    _outputTransportRoute, _transportRouteProvenance, provenancePkg, _namePkg,
    _signatureCert⟩ := carrier
  have auditUnary : UnaryHistory audit :=
    unary_cont_closed outputUnary routeUnary outputRouteAudit
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row audit ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row signature ∨ hsame row eliminator ∨ hsame row motive ∨
              hsame row branch ∨ hsame row descent ∨ hsame row output ∨ hsame row audit)
          (fun row : BHist => hsame row audit ∧ PkgSig bundle audit pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro audit ⟨hsame_refl audit, auditUnary⟩
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
        exact ⟨hsame_trans (hsame_symm same) source.left,
          unary_transport source.right same⟩
    }
    pattern_sound := by
      intro row source
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, auditPkg⟩
  }
  exact
    ⟨cert, signatureUnary, eliminatorUnary, motiveUnary, branchUnary, descentUnary,
      outputUnary, auditUnary, provenancePkg, auditPkg⟩

theorem RecursionAuthorizationLedgerCarrier_signature_acceptance [AskSetup] [PackageSetup]
    {signature recursor motive branches descent output transport routes provenance name
      branchAudit : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature recursor motive branches descent output
        transport routes provenance name bundle pkg ->
      Cont recursor branches branchAudit ->
        PkgSig bundle branchAudit pkg ->
          UnaryHistory signature ∧ UnaryHistory recursor ∧ UnaryHistory branches ∧
            UnaryHistory branchAudit ∧ Cont signature recursor motive ∧
              Cont recursor branches branchAudit ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle branchAudit pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier branchRoute branchPkg
  obtain ⟨signatureUnary, recursorUnary, _motiveUnary, branchesUnary, _descentUnary,
    _outputUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    signatureRoute, _branchDescentOutput, _outputTransportRoutes, _transportRoutesProvenance,
    provenancePkg, _namePkg, _semanticCert⟩ := carrier
  have branchAuditUnary : UnaryHistory branchAudit :=
    unary_cont_closed recursorUnary branchesUnary branchRoute
  exact
    ⟨signatureUnary,
      recursorUnary,
      branchesUnary,
      branchAuditUnary,
      signatureRoute,
      branchRoute,
      provenancePkg,
      branchPkg⟩

theorem RecursionAuthorizationLedgerCarrier_audit_provenance_exhaustion
    [AskSetup] [PackageSetup]
    {signature recursor motive branches descent output transport routes provenance name
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature recursor motive branches descent output
        transport routes provenance name bundle pkg →
      Cont transport routes auditRead →
        PkgSig bundle auditRead pkg →
          UnaryHistory transport ∧ UnaryHistory routes ∧ UnaryHistory provenance ∧
            UnaryHistory auditRead ∧ Cont transport routes provenance ∧
              Cont transport routes auditRead ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle name pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier transportRoutesAudit auditPkg
  obtain ⟨_signatureUnary, _recursorUnary, _motiveUnary, _branchesUnary, _descentUnary,
    _outputUnary, transportUnary, routesUnary, provenanceUnary, _nameUnary,
    _signatureRecursorMotive, _branchesDescentOutput, _outputTransportRoutes,
    transportRoutesProvenance, provenancePkg, namePkg, _semanticCert⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed transportUnary routesUnary transportRoutesAudit
  exact
    ⟨transportUnary, routesUnary, provenanceUnary, auditUnary, transportRoutesProvenance,
      transportRoutesAudit, provenancePkg, namePkg, auditPkg⟩

theorem RecursionAuthorizationLedgerCarrier_generator_closure_sibling_route
    [AskSetup] [PackageSetup]
    {signature recursor motive branches descent output transport routes provenance name
      branchRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature recursor motive branches descent output
        transport routes provenance name bundle pkg ->
      Cont recursor branches branchRead ->
        PkgSig bundle branchRead pkg ->
          UnaryHistory signature ∧ UnaryHistory recursor ∧ UnaryHistory branches ∧
            UnaryHistory descent ∧ UnaryHistory output ∧ UnaryHistory branchRead ∧
              Cont signature recursor motive ∧ Cont recursor branches branchRead ∧
                Cont branches descent output ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle branchRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig
  intro carrier recursorBranchesRead branchPkg
  obtain ⟨signatureUnary, recursorUnary, _motiveUnary, branchesUnary, descentUnary,
    outputUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    signatureRecursorMotive, branchesDescentOutput, _outputTransportRoutes,
    _transportRoutesProvenance, provenancePkg, _namePkg, _semanticCert⟩ := carrier
  have branchReadUnary : UnaryHistory branchRead :=
    unary_cont_closed recursorUnary branchesUnary recursorBranchesRead
  exact
    ⟨signatureUnary,
      recursorUnary,
      branchesUnary,
      descentUnary,
      outputUnary,
      branchReadUnary,
      signatureRecursorMotive,
      recursorBranchesRead,
      branchesDescentOutput,
      provenancePkg,
      branchPkg⟩

theorem RecursionAuthorizationLedgerCarrier_consumer_nonescape [AskSetup] [PackageSetup]
    {signature eliminator motive branches descent output transport routes provenance name
      consumer : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RecursionAuthorizationLedgerCarrier signature eliminator motive branches descent output
        transport routes provenance name bundle pkg →
      Cont descent output consumer →
        PkgSig bundle consumer pkg →
          UnaryHistory signature ∧ UnaryHistory eliminator ∧ UnaryHistory motive ∧
            UnaryHistory branches ∧ UnaryHistory descent ∧ UnaryHistory output ∧
              UnaryHistory consumer ∧ Cont signature eliminator motive ∧
                Cont branches descent output ∧ Cont descent output consumer ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle consumer pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig UnaryHistory
  intro carrier descentOutputConsumer consumerPkg
  obtain ⟨signatureUnary, eliminatorUnary, motiveUnary, branchesUnary, descentUnary,
    outputUnary, _transportUnary, _routesUnary, _provenanceUnary, _nameUnary,
    signatureEliminatorMotive, branchesDescentOutput, _outputTransportRoutes,
    _transportRoutesProvenance, provenancePkg, _namePkg, _semanticCert⟩ :=
    carrier
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed descentUnary outputUnary descentOutputConsumer
  exact
    ⟨signatureUnary,
      eliminatorUnary,
      motiveUnary,
      branchesUnary,
      descentUnary,
      outputUnary,
      consumerUnary,
      signatureEliminatorMotive,
      branchesDescentOutput,
      descentOutputConsumer,
      provenancePkg,
      consumerPkg⟩

end BEDC.Derived.RecursionAuthorizationLedgerUp
