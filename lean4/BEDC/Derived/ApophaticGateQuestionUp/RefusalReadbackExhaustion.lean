import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_refusal_readback_exhaustion
    [AskSetup] [PackageSetup]
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
                        hsame row refusal ∧
                          ApophaticGateQuestionCarrier socket question refusal readback
                            transport route provenance nameRow bundle pkg)
                      (fun row : BHist =>
                        hsame row refusal ∧ UnaryHistory row ∧
                          Cont question refusal route)
                      (fun row : BHist =>
                        PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg ∧
                          hsame row refusal)
                      hsame ∧
                    UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                      UnaryHistory readback ∧ UnaryHistory auditRead ∧
                        UnaryHistory refusalRead ∧ UnaryHistory rootRead ∧
                          Cont question refusal route ∧
                            Cont refusal readback refusalRead ∧
                              Cont readback route auditRead ∧
                                Cont route provenance rootRead ∧
                                  PkgSig bundle provenance pkg ∧
                                    PkgSig bundle auditRead pkg ∧
                                      PkgSig bundle refusalRead pkg ∧
                                        PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier auditRoute refusalRoute rootRoute auditPkg refusalPkg rootPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary readbackUnary refusalRoute
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary rootRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row refusal ∧
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg)
          (fun row : BHist =>
            hsame row refusal ∧ UnaryHistory row ∧ Cont question refusal route)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg ∧
              hsame row refusal)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro refusal ⟨hsame_refl refusal, carrierPacket⟩
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
          ⟨source.left, unary_transport refusalUnary (hsame_symm source.left),
            questionRefusalRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, refusalPkg, source.left⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, auditUnary,
      refusalReadUnary, rootReadUnary, questionRefusalRoute, refusalRoute, auditRoute,
      rootRoute, provenancePkg, auditPkg, refusalPkg, rootPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
