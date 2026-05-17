import BEDC.Derived.ApophaticGateQuestionUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_audit_readback_cut [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditCut cutTransport
      cutName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditCut →
        Cont auditCut transport cutTransport →
          Cont cutTransport nameRow cutName →
            PkgSig bundle cutName pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticGateQuestionCarrier socket question refusal readback transport route
                      provenance nameRow bundle pkg ∧ hsame row auditCut)
                  (fun row : BHist => hsame row auditCut ∧ UnaryHistory row)
                  (fun _row : BHist =>
                    Cont readback route auditCut ∧ Cont auditCut transport cutTransport ∧
                      Cont cutTransport nameRow cutName ∧ PkgSig bundle provenance pkg ∧
                        PkgSig bundle cutName pkg)
                  hsame ∧
                UnaryHistory readback ∧ UnaryHistory auditCut ∧ UnaryHistory cutTransport ∧
                  UnaryHistory cutName ∧ Cont readback route auditCut ∧
                    Cont auditCut transport cutTransport ∧
                      Cont cutTransport nameRow cutName ∧ hsame readback (append socket question) ∧
                        PkgSig bundle provenance pkg ∧ PkgSig bundle cutName pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackRouteAudit auditTransport cutNameRoute cutNamePkg
  have carrierWitness :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _questionUnary, _refusalUnary, readbackUnary, transportUnary,
    routeUnary, _provenanceUnary, nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditCut :=
    unary_cont_closed readbackUnary routeUnary readbackRouteAudit
  have cutTransportUnary : UnaryHistory cutTransport :=
    unary_cont_closed auditUnary transportUnary auditTransport
  have cutNameUnary : UnaryHistory cutName :=
    unary_cont_closed cutTransportUnary nameRowUnary cutNameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row auditCut)
          (fun row : BHist => hsame row auditCut ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont readback route auditCut ∧ Cont auditCut transport cutTransport ∧
              Cont cutTransport nameRow cutName ∧ PkgSig bundle provenance pkg ∧
                PkgSig bundle cutName pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro auditCut ⟨carrierWitness, hsame_refl auditCut⟩
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
        exact ⟨source.right, unary_transport auditUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row _source
        exact
          ⟨readbackRouteAudit, auditTransport, cutNameRoute, provenancePkg, cutNamePkg⟩
    }
  exact
    ⟨cert, readbackUnary, auditUnary, cutTransportUnary, cutNameUnary, readbackRouteAudit,
      auditTransport, cutNameRoute, readbackSameSourceQuestion, provenancePkg, cutNamePkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
