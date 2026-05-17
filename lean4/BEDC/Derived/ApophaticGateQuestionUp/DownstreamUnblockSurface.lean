import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_downstream_unblock_surface
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead
      unblockRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        Cont auditRead provenance unblockRead →
          PkgSig bundle unblockRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticGateQuestionCarrier socket question refusal readback transport
                    route provenance nameRow bundle pkg ∧ hsame row unblockRead)
                (fun row : BHist =>
                  hsame row unblockRead ∧ UnaryHistory row ∧ Cont readback route auditRead ∧
                    Cont auditRead provenance unblockRead)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle unblockRead pkg ∧
                    hsame row unblockRead)
                hsame ∧
              UnaryHistory auditRead ∧ UnaryHistory unblockRead ∧
                hsame readback (append socket question) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackRouteAudit auditProvenanceUnblock unblockPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteAudit
  have unblockUnary : UnaryHistory unblockRead :=
    unary_cont_closed auditUnary provenanceUnary auditProvenanceUnblock
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row unblockRead)
          (fun row : BHist =>
            hsame row unblockRead ∧ UnaryHistory row ∧ Cont readback route auditRead ∧
              Cont auditRead provenance unblockRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle unblockRead pkg ∧
              hsame row unblockRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro unblockRead ⟨carrierPacket, hsame_refl unblockRead⟩
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
          ⟨source.right, unary_transport unblockUnary (hsame_symm source.right),
            readbackRouteAudit, auditProvenanceUnblock⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, unblockPkg, source.right⟩
    }
  exact ⟨cert, auditUnary, unblockUnary, readbackSameSourceQuestion⟩

end BEDC.Derived.ApophaticGateQuestionUp
