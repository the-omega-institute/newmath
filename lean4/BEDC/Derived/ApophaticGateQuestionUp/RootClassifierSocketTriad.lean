import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_classifier_socket_triad [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row refusal ∧ hsame readback (append socket question)) ∧
                  ApophaticGateQuestionCarrier socket question refusal readback transport route
                    provenance nameRow bundle pkg)
              (fun row : BHist =>
                hsame row refusal ∧ UnaryHistory row ∧ Cont question refusal route ∧
                  Cont readback route auditRead)
              (fun row : BHist =>
                hsame row refusal ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle auditRead pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory refusal ∧ UnaryHistory readback ∧
              UnaryHistory auditRead ∧ Cont socket question readback ∧
                Cont question refusal route ∧ Cont readback route auditRead ∧
                  hsame readback (append socket question) ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier auditRoute auditPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, _questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row refusal ∧ hsame readback (append socket question)) ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row refusal ∧ UnaryHistory row ∧ Cont question refusal route ∧
              Cont readback route auditRead)
          (fun row : BHist =>
            hsame row refusal ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle auditRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro refusal
            ⟨⟨hsame_refl refusal, readbackSameSourceQuestion⟩, carrierPacket⟩
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
          exact
            ⟨⟨hsame_trans (hsame_symm same) source.left.left, source.left.right⟩,
              source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left.left, unary_transport refusalUnary (hsame_symm source.left.left),
            questionRefusalRoute, auditRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left.left, provenancePkg, auditPkg⟩
    }
  exact
    ⟨cert, socketUnary, refusalUnary, readbackUnary, auditReadUnary,
      socketQuestionReadback, questionRefusalRoute, auditRoute, readbackSameSourceQuestion,
      provenancePkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
