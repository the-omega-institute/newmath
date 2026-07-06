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

end BEDC.Derived.BareObjectRefusalUp
