import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_refusal_ledger_transport [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow refusal' refusalRead
      auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      hsame refusal refusal' →
        Cont question refusal refusalRead →
          Cont readback route auditRead →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticGateQuestionCarrier socket question refusal readback transport route
                        provenance nameRow bundle pkg ∧
                      hsame row refusal')
                  (fun row : BHist =>
                    hsame row refusal' ∧ UnaryHistory row ∧
                      Cont question refusal refusalRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                      hsame row refusal')
                  hsame ∧
                UnaryHistory refusal' ∧ UnaryHistory refusalRead ∧ UnaryHistory auditRead ∧
                  Cont question refusal refusalRead ∧ Cont readback route auditRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier sameRefusal questionRefusalRead readbackRouteAudit auditPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have refusalUnary' : UnaryHistory refusal' :=
    unary_transport refusalUnary sameRefusal
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed questionUnary refusalUnary questionRefusalRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteAudit
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg ∧
              hsame row refusal')
          (fun row : BHist =>
            hsame row refusal' ∧ UnaryHistory row ∧ Cont question refusal refusalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
              hsame row refusal')
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro refusal' ⟨carrierPacket, hsame_refl refusal'⟩
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
          ⟨source.right, unary_transport refusalUnary' (hsame_symm source.right),
            questionRefusalRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, auditPkg, source.right⟩
    }
  exact
    ⟨cert, refusalUnary', refusalReadUnary, auditReadUnary, questionRefusalRead,
      readbackRouteAudit⟩

end BEDC.Derived.ApophaticGateQuestionUp
