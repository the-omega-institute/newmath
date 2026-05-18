import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_visible_socket_triad [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        PkgSig bundle auditRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row socket ∧ hsame readback (append socket question)) ∧
                  ApophaticGateQuestionCarrier socket question refusal readback transport route
                    provenance nameRow bundle pkg)
              (fun row : BHist =>
                hsame row socket ∧ UnaryHistory row ∧ Cont socket question readback)
              (fun row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧
                  hsame row socket)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
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
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row socket ∧ hsame readback (append socket question)) ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row socket ∧ UnaryHistory row ∧ Cont socket question readback)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle auditRead pkg ∧ hsame row socket)
          hsame := by
    constructor
    · constructor
      · exact
          Exists.intro socket
            ⟨⟨hsame_refl socket, readbackSameSourceQuestion⟩, carrierPacket⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact
          ⟨⟨hsame_trans (hsame_symm same) source.left.left, source.left.right⟩,
            source.right⟩
    · intro row source
      have rowSameSocket : hsame row socket := source.left.left
      exact
        ⟨rowSameSocket, unary_transport socketUnary (hsame_symm rowSameSocket),
          socketQuestionReadback⟩
    · intro row source
      exact ⟨provenancePkg, auditPkg, source.left.left⟩
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, auditUnary, socketQuestionReadback,
      questionRefusalRoute, auditRoute, readbackSameSourceQuestion, provenancePkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
