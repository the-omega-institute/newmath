import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_visible_socket_nonescape [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow socketRead auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question socketRead →
        Cont readback route auditRead →
          PkgSig bundle auditRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  hsame row socketRead ∧
                    ApophaticGateQuestionCarrier socket question refusal readback transport route
                      provenance nameRow bundle pkg)
                (fun row : BHist =>
                  hsame row socketRead ∧ UnaryHistory row ∧ Cont socket question socketRead ∧
                    Cont readback route auditRead)
                (fun row : BHist =>
                  hsame row socketRead ∧ PkgSig bundle provenance pkg ∧
                    PkgSig bundle auditRead pkg)
                hsame ∧
              UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                UnaryHistory readback ∧ UnaryHistory socketRead ∧ UnaryHistory auditRead ∧
                  Cont socket question socketRead ∧ Cont readback route auditRead ∧
                    hsame readback (append socket question) ∧ PkgSig bundle provenance pkg ∧
                      PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketQuestionRead auditRoute auditPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have socketReadUnary : UnaryHistory socketRead :=
    unary_cont_closed socketUnary questionUnary socketQuestionRead
  have auditReadUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row socketRead ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row socketRead ∧ UnaryHistory row ∧ Cont socket question socketRead ∧
              Cont readback route auditRead)
          (fun row : BHist =>
            hsame row socketRead ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle auditRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro socketRead ⟨hsame_refl socketRead, carrierPacket⟩
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
          exact ⟨hsame_trans (hsame_symm same) source.left, source.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.left, unary_transport socketReadUnary (hsame_symm source.left),
            socketQuestionRead, auditRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨source.left, provenancePkg, auditPkg⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, socketReadUnary,
      auditReadUnary, socketQuestionRead, auditRoute, readbackSameSourceQuestion,
      provenancePkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
