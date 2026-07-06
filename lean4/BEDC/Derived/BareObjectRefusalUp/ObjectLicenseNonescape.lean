import BEDC.Derived.BareObjectRefusalUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BareObjectRefusalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def BareObjectRefusalCarrier
    (objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName : BHist) :
    Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory objectName ∧ UnaryHistory missingFields ∧ UnaryHistory refusal ∧
    UnaryHistory witnessAudit ∧ UnaryHistory ledger ∧ UnaryHistory transport ∧
      UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont missingFields refusal witnessAudit ∧ Cont routes provenance localName

theorem BareObjectRefusalCarrier_object_license_nonescape
    {objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName : BHist} :
    BareObjectRefusalCarrier objectName missingFields refusal witnessAudit ledger transport
        routes provenance localName ->
      UnaryHistory objectName ∧ UnaryHistory missingFields ∧ UnaryHistory refusal ∧
        UnaryHistory witnessAudit ∧ UnaryHistory ledger ∧
          Cont missingFields refusal witnessAudit ∧ Cont routes provenance localName := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier
  obtain ⟨objectUnary, missingUnary, refusalUnary, witnessUnary, ledgerUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _localNameUnary, witnessRoute,
    localNameRoute⟩ := carrier
  exact
    ⟨objectUnary, missingUnary, refusalUnary, witnessUnary, ledgerUnary, witnessRoute,
      localNameRoute⟩

theorem BareObjectRefusalCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName nameRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BareObjectRefusalCarrier objectName missingFields refusal witnessAudit ledger transport
        routes provenance localName ->
      PkgSig bundle provenance pkg ->
        PkgSig bundle localName pkg ->
          Cont routes provenance nameRead ->
            SemanticNameCert
                (fun row : BHist => hsame row localName ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row objectName ∨
                    hsame row missingFields ∨
                      hsame row refusal ∨
                        hsame row witnessAudit ∨
                          hsame row ledger ∨
                            hsame row transport ∨
                              hsame row routes ∨ hsame row provenance ∨ hsame row localName)
                (fun row : BHist =>
                  UnaryHistory row ∧ PkgSig bundle localName pkg ∧
                    Cont routes provenance nameRead)
                hsame ∧
              UnaryHistory nameRead ∧ Cont missingFields refusal witnessAudit := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro carrier _provenancePkg localPkg nameRoute
  obtain ⟨objectUnary, missingUnary, refusalUnary, _witnessUnary, _ledgerUnary,
    _transportUnary, routesUnary, provenanceUnary, localUnary, witnessRoute,
    _localNameRoute⟩ := carrier
  have nameUnary : UnaryHistory nameRead :=
    unary_cont_closed routesUnary provenanceUnary nameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row objectName ∨
              hsame row missingFields ∨
                hsame row refusal ∨
                  hsame row witnessAudit ∨
                    hsame row ledger ∨
                      hsame row transport ∨
                        hsame row routes ∨ hsame row provenance ∨ hsame row localName)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle localName pkg ∧ Cont routes provenance nameRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro localName ⟨hsame_refl localName, localUnary⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact
          ⟨hsame_trans (hsame_symm same) source.left,
            unary_transport source.right same⟩
    · intro row source
      have sameLocal : hsame row localName := source.left
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr (Or.inr sameLocal)))))))
    · intro _row source
      exact ⟨source.right, localPkg, nameRoute⟩
  exact ⟨cert, nameUnary, witnessRoute⟩

theorem BareObjectRefusalCarrier_obligation_classifier
    {objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName classifierRead : BHist} :
    BareObjectRefusalCarrier objectName missingFields refusal witnessAudit ledger transport
        routes provenance localName ->
      Cont missingFields refusal classifierRead ->
        UnaryHistory missingFields ∧ UnaryHistory refusal ∧ UnaryHistory classifierRead ∧
          hsame classifierRead witnessAudit ∧ Cont missingFields refusal witnessAudit := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame
  intro carrier classifierRoute
  obtain ⟨_objectUnary, missingUnary, refusalUnary, _witnessUnary, _ledgerUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _localUnary, witnessRoute,
    _localRoute⟩ := carrier
  have classifierUnary : UnaryHistory classifierRead :=
    unary_cont_closed missingUnary refusalUnary classifierRoute
  have sameClassifierWitness : hsame classifierRead witnessAudit :=
    cont_deterministic classifierRoute witnessRoute
  exact ⟨missingUnary, refusalUnary, classifierUnary, sameClassifierWitness, witnessRoute⟩

theorem BareObjectRefusalCarrier_obligation_carrier
    {objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName licenseRead refusalRead nameRead : BHist} :
    BareObjectRefusalCarrier objectName missingFields refusal witnessAudit ledger transport
        routes provenance localName ->
      Cont objectName missingFields licenseRead ->
        Cont refusal ledger refusalRead ->
          Cont routes provenance nameRead ->
            UnaryHistory objectName ∧ UnaryHistory missingFields ∧ UnaryHistory refusal ∧
              UnaryHistory witnessAudit ∧ UnaryHistory ledger ∧ UnaryHistory transport ∧
                UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
                  UnaryHistory licenseRead ∧ UnaryHistory refusalRead ∧
                    UnaryHistory nameRead ∧ Cont missingFields refusal witnessAudit ∧
                      Cont routes provenance localName := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro carrier licenseRoute refusalRoute nameRoute
  obtain ⟨objectUnary, missingUnary, refusalUnary, witnessUnary, ledgerUnary,
    transportUnary, routesUnary, provenanceUnary, localUnary, witnessRoute,
    localRoute⟩ := carrier
  have licenseUnary : UnaryHistory licenseRead :=
    unary_cont_closed objectUnary missingUnary licenseRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary ledgerUnary refusalRoute
  have nameReadUnary : UnaryHistory nameRead :=
    unary_cont_closed routesUnary provenanceUnary nameRoute
  exact
    ⟨objectUnary, missingUnary, refusalUnary, witnessUnary, ledgerUnary, transportUnary,
      routesUnary, provenanceUnary, localUnary, licenseUnary, refusalReadUnary, nameReadUnary,
      witnessRoute, localRoute⟩

theorem BareObjectRefusalCarrier_obligation_ledger
    {objectName missingFields refusal witnessAudit ledger transport routes provenance
      localName ledgerRead auditRead : BHist} :
    BareObjectRefusalCarrier objectName missingFields refusal witnessAudit ledger transport
        routes provenance localName ->
      Cont witnessAudit ledger auditRead ->
        Cont auditRead refusal ledgerRead ->
          UnaryHistory witnessAudit ∧ UnaryHistory ledger ∧ UnaryHistory auditRead ∧
            UnaryHistory ledgerRead ∧
              hsame ledgerRead (append (append witnessAudit ledger) refusal) := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory hsame append
  intro carrier auditRoute ledgerRoute
  obtain ⟨_objectUnary, _missingUnary, refusalUnary, witnessUnary, ledgerUnary,
    _transportUnary, _routesUnary, _provenanceUnary, _localUnary, _witnessRoute,
    _localRoute⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed witnessUnary ledgerUnary auditRoute
  have ledgerReadUnary : UnaryHistory ledgerRead :=
    unary_cont_closed auditUnary refusalUnary ledgerRoute
  have ledgerExact : hsame ledgerRead (append (append witnessAudit ledger) refusal) := by
    rw [ledgerRoute, auditRoute]
    exact hsame_refl (append (append witnessAudit ledger) refusal)
  exact ⟨witnessUnary, ledgerUnary, auditUnary, ledgerReadUnary, ledgerExact⟩

end BEDC.Derived.BareObjectRefusalUp
