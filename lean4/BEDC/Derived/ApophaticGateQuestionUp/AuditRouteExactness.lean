import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_audit_route_exactness [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticGateQuestionCarrier socket question refusal readback transport route
                  provenance nameRow bundle pkg ∧ hsame row readback)
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont socket question readback ∧ Cont readback route auditRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
              UnaryHistory readback ∧ UnaryHistory auditRead ∧
                Cont socket question readback ∧ Cont question refusal route ∧
                  Cont readback route auditRead ∧ hsame readback (append socket question) ∧
                    PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier auditRoute auditPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row readback)
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket question readback ∧ Cont readback route auditRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro readback ⟨carrierPacket, hsame_refl readback⟩
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
        exact ⟨source.right, unary_transport readbackUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨socketQuestionReadback, auditRoute, provenancePkg, auditPkg⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, auditUnary,
      socketQuestionReadback, questionRefusalRoute, auditRoute, readbackSameSourceQuestion,
      provenancePkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
