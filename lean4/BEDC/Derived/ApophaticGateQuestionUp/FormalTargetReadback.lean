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

theorem ApophaticGateQuestionCarrier_formal_target_readback [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead refusalRead
      rootRead finalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont refusal readback refusalRead →
        Cont readback route auditRead →
          Cont route provenance rootRead →
            Cont auditRead nameRow finalRead →
              PkgSig bundle auditRead pkg →
                PkgSig bundle refusalRead pkg →
                  PkgSig bundle rootRead pkg →
                    PkgSig bundle finalRead pkg →
                      SemanticNameCert
                          (fun row : BHist =>
                            hsame row finalRead ∧
                              ApophaticGateQuestionCarrier socket question refusal readback
                                transport route provenance nameRow bundle pkg)
                          (fun row : BHist =>
                            hsame row finalRead ∧ UnaryHistory row ∧
                              Cont auditRead nameRow finalRead)
                          (fun row : BHist =>
                            PkgSig bundle finalRead pkg ∧ hsame row finalRead ∧
                              PkgSig bundle provenance pkg)
                          hsame ∧
                        UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                          UnaryHistory readback ∧ UnaryHistory auditRead ∧
                            UnaryHistory refusalRead ∧ UnaryHistory rootRead ∧
                              UnaryHistory finalRead ∧ Cont socket question readback ∧
                                Cont question refusal route ∧
                                  Cont refusal readback refusalRead ∧
                                    Cont readback route auditRead ∧
                                      Cont route provenance rootRead ∧
                                        Cont auditRead nameRow finalRead ∧
                                          hsame readback (append socket question) ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle auditRead pkg ∧
                                                PkgSig bundle refusalRead pkg ∧
                                                  PkgSig bundle rootRead pkg ∧
                                                    PkgSig bundle finalRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier refusalReadbackRead readbackRouteAudit routeProvenanceRoot
    auditNameFinal auditPkg refusalPkg rootPkg finalPkg
  have carrierWitness :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    _refusalReadbackTransport, _readbackRouteNameRow, readbackSameSourceQuestion,
    provenancePkg⟩ := carrier
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary readbackUnary refusalReadbackRead
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteAudit
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceRoot
  have finalUnary : UnaryHistory finalRead :=
    unary_cont_closed auditUnary nameRowUnary auditNameFinal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row finalRead ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row finalRead ∧ UnaryHistory row ∧ Cont auditRead nameRow finalRead)
          (fun row : BHist =>
            PkgSig bundle finalRead pkg ∧ hsame row finalRead ∧
              PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro finalRead ⟨hsame_refl finalRead, carrierWitness⟩
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
          ⟨source.left, unary_transport finalUnary (hsame_symm source.left),
            auditNameFinal⟩
      ledger_sound := by
        intro _row source
        exact ⟨finalPkg, source.left, provenancePkg⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, auditUnary,
      refusalReadUnary, rootUnary, finalUnary, socketQuestionReadback, questionRefusalRoute,
      refusalReadbackRead, readbackRouteAudit, routeProvenanceRoot, auditNameFinal,
      readbackSameSourceQuestion, provenancePkg, auditPkg, refusalPkg, rootPkg, finalPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
