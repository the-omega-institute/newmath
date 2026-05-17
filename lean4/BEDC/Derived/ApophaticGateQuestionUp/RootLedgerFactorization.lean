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

theorem ApophaticGateQuestionCarrier_root_ledger_factorization [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow auditRead refusalRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route auditRead →
        Cont refusal readback refusalRead →
          Cont route provenance rootRead →
            PkgSig bundle auditRead pkg →
              PkgSig bundle refusalRead pkg →
                PkgSig bundle rootRead pkg →
                  SemanticNameCert
                      (fun row : BHist =>
                        hsame row refusalRead ∧
                          ApophaticGateQuestionCarrier socket question refusal readback transport
                            route provenance nameRow bundle pkg)
                      (fun row : BHist =>
                        hsame row refusalRead ∧ UnaryHistory row ∧
                          Cont refusal readback refusalRead)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg ∧
                          PkgSig bundle rootRead pkg ∧ hsame row refusalRead)
                      hsame ∧
                    UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                      UnaryHistory readback ∧ UnaryHistory auditRead ∧
                        UnaryHistory refusalRead ∧ UnaryHistory rootRead ∧
                          Cont socket question readback ∧ Cont question refusal route ∧
                            Cont refusal readback refusalRead ∧
                              Cont readback route auditRead ∧
                                Cont route provenance rootRead ∧
                                  hsame readback (append socket question) ∧
                                    PkgSig bundle provenance pkg ∧
                                      PkgSig bundle auditRead pkg ∧
                                        PkgSig bundle refusalRead pkg ∧
                                          PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackRouteAudit refusalReadbackRead routeProvenanceRoot auditPkg
    refusalPkg rootPkg
  have carrierWitness :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    _refusalReadbackTransport, _readbackRouteNameRow, readbackSameSourceQuestion,
    provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteAudit
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary readbackUnary refusalReadbackRead
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary routeProvenanceRoot
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusalRead ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row refusalRead ∧ UnaryHistory row ∧ Cont refusal readback refusalRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg ∧
              PkgSig bundle rootRead pkg ∧ hsame row refusalRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro refusalRead ⟨hsame_refl refusalRead, carrierWitness⟩
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
          ⟨source.left, unary_transport refusalReadUnary (hsame_symm source.left),
            refusalReadbackRead⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, refusalPkg, rootPkg, source.left⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, auditUnary,
      refusalReadUnary, rootUnary, socketQuestionReadback, questionRefusalRoute,
      refusalReadbackRead, readbackRouteAudit, routeProvenanceRoot,
      readbackSameSourceQuestion, provenancePkg, auditPkg, refusalPkg, rootPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
