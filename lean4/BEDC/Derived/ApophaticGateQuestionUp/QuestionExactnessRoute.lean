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

theorem ApophaticGateQuestionCarrier_question_exactness_route [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow questionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question questionRead →
        PkgSig bundle questionRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticGateQuestionCarrier socket question refusal readback transport route
                  provenance nameRow bundle pkg ∧ hsame row question)
              (fun row : BHist => hsame row question ∧ UnaryHistory row)
              (fun _row : BHist =>
                PkgSig bundle provenance pkg ∧ PkgSig bundle questionRead pkg ∧
                  Cont socket question questionRead)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory questionRead ∧
              Cont socket question questionRead ∧ hsame readback (append socket question) ∧
                PkgSig bundle questionRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketQuestionRead questionReadPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, _refusalUnary, _readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have questionReadUnary : UnaryHistory questionRead :=
    unary_cont_closed socketUnary questionUnary socketQuestionRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row question)
          (fun row : BHist => hsame row question ∧ UnaryHistory row)
          (fun _row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle questionRead pkg ∧
              Cont socket question questionRead)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro question ⟨carrierPacket, hsame_refl question⟩
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
          ⟨source.right, unary_transport questionUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row _source
        exact ⟨provenancePkg, questionReadPkg, socketQuestionRead⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, questionReadUnary, socketQuestionRead,
      readbackSameSourceQuestion, questionReadPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
