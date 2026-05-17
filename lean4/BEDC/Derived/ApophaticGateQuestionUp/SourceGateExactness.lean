import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_source_gate_exactness [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow sourceGate : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question sourceGate →
        PkgSig bundle sourceGate pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticGateQuestionCarrier socket question refusal readback transport route
                  provenance nameRow bundle pkg ∧ hsame row question)
              (fun row : BHist => hsame row question ∧ UnaryHistory row)
              (fun row : BHist =>
                Cont socket question sourceGate ∧ hsame row question ∧
                  PkgSig bundle provenance pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory sourceGate ∧
              Cont socket question sourceGate ∧ hsame readback (append socket question) ∧
                PkgSig bundle sourceGate pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame
  intro carrier sourceGateRoute sourceGatePkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, _refusalUnary, _readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have sourceGateUnary : UnaryHistory sourceGate :=
    unary_cont_closed socketUnary questionUnary sourceGateRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row question)
          (fun row : BHist => hsame row question ∧ UnaryHistory row)
          (fun row : BHist =>
            Cont socket question sourceGate ∧ hsame row question ∧
              PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro question ⟨carrierPacket, hsame_refl question⟩
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
        exact ⟨source.right, unary_transport questionUnary (hsame_symm source.right)⟩
      ledger_sound := by
        intro _row source
        exact ⟨sourceGateRoute, source.right, provenancePkg⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, sourceGateUnary, sourceGateRoute,
      readbackSameSourceQuestion, sourceGatePkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
