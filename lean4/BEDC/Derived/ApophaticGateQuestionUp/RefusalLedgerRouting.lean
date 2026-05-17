import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_refusal_ledger_routing
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow refusalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont refusal readback refusalRead →
        SemanticNameCert
            (fun row : BHist =>
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg ∧ hsame row refusal)
            (fun row : BHist =>
              hsame row refusal ∧ UnaryHistory row ∧ Cont socket question readback)
            (fun _row : BHist =>
              hsame readback (append socket question) ∧ PkgSig bundle provenance pkg)
            hsame ∧
          UnaryHistory refusalRead ∧ Cont refusal readback refusalRead ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier refusalRoute
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _questionUnary, refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary readbackUnary refusalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row refusal)
          (fun row : BHist =>
            hsame row refusal ∧ UnaryHistory row ∧ Cont socket question readback)
          (fun _row : BHist =>
            hsame readback (append socket question) ∧ PkgSig bundle provenance pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro refusal ⟨carrierPacket, hsame_refl refusal⟩
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
          ⟨source.right, unary_transport refusalUnary (hsame_symm source.right),
            socketQuestionReadback⟩
      ledger_sound := by
        intro _row _source
        exact ⟨readbackSameSourceQuestion, provenancePkg⟩
    }
  exact ⟨cert, refusalReadUnary, refusalRoute, provenancePkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
