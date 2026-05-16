import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_audit_readback_locality [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback nameRow localRead →
        PkgSig bundle localRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticGateQuestionCarrier socket question refusal readback transport route
                  provenance nameRow bundle pkg ∧ hsame row readback)
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont socket question readback ∧ hsame row readback ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory readback ∧ UnaryHistory localRead ∧ Cont socket question readback ∧
              Cont readback nameRow localRead ∧ hsame readback (append socket question) ∧
                PkgSig bundle localRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackNameLocal localPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, provenanceUnary, nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed readbackUnary nameRowUnary readbackNameLocal
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row readback)
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont socket question readback ∧ hsame row readback ∧
              PkgSig bundle provenance pkg)
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
        intro _row source
        exact ⟨socketQuestionReadback, source.right, provenancePkg⟩
    }
  exact
    ⟨cert, readbackUnary, localUnary, socketQuestionReadback, readbackNameLocal,
      readbackSameSourceQuestion, localPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
