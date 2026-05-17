import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_unblock_package [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead auditRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont route provenance rootRead →
        Cont readback route auditRead →
          PkgSig bundle rootRead pkg →
            PkgSig bundle auditRead pkg →
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticGateQuestionCarrier socket question refusal readback transport
                      route provenance nameRow bundle pkg ∧ hsame row rootRead)
                  (fun row : BHist =>
                    hsame row rootRead ∧ UnaryHistory row ∧ Cont route provenance rootRead)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                      PkgSig bundle auditRead pkg ∧ hsame row rootRead)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                  UnaryHistory readback ∧ UnaryHistory rootRead ∧ UnaryHistory auditRead ∧
                    Cont socket question readback ∧ Cont question refusal route ∧
                      Cont route provenance rootRead ∧ Cont readback route auditRead ∧
                        hsame readback (append socket question) ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                            PkgSig bundle auditRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier rootRoute auditRoute rootPkg auditPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, provenanceUnary, _nameRowUnary, socketQuestionReadback, questionRefusalRoute,
    _refusalReadbackTransport, _readbackRouteNameRow, readbackSameSourceQuestion,
    provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed routeUnary provenanceUnary rootRoute
  have auditUnary : UnaryHistory auditRead :=
    unary_cont_closed readbackUnary routeUnary auditRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row rootRead)
          (fun row : BHist =>
            hsame row rootRead ∧ UnaryHistory row ∧ Cont route provenance rootRead)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              PkgSig bundle auditRead pkg ∧ hsame row rootRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro rootRead ⟨carrierPacket, hsame_refl rootRead⟩
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
          ⟨source.right, unary_transport rootUnary (hsame_symm source.right), rootRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, rootPkg, auditPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, rootUnary, auditUnary,
      socketQuestionReadback, questionRefusalRoute, rootRoute, auditRoute,
      readbackSameSourceQuestion, provenancePkg, rootPkg, auditPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
