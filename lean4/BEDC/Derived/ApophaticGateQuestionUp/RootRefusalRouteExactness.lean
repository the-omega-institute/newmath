import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_refusal_route_exactness [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow refusalRead
      rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont refusal readback refusalRead →
        Cont refusalRead provenance rootRead →
          PkgSig bundle rootRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticGateQuestionCarrier socket question refusal readback transport route
                    provenance nameRow bundle pkg ∧ hsame row refusal)
                (fun row : BHist =>
                  hsame row refusal ∧ UnaryHistory row ∧ Cont question refusal route)
                (fun row : BHist =>
                  PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
                    hsame row refusal)
                hsame ∧
              UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory refusal ∧
                UnaryHistory readback ∧ UnaryHistory refusalRead ∧ UnaryHistory rootRead ∧
                  Cont socket question readback ∧ Cont question refusal route ∧
                    Cont refusal readback refusalRead ∧
                      Cont refusalRead provenance rootRead ∧
                        hsame readback (append socket question) ∧
                          PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier refusalReadRoute rootReadRoute rootPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, provenanceUnary, _nameRowUnary, socketQuestionReadback,
    questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary readbackUnary refusalReadRoute
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed refusalReadUnary provenanceUnary rootReadRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row refusal)
          (fun row : BHist =>
            hsame row refusal ∧ UnaryHistory row ∧ Cont question refusal route)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg ∧
              hsame row refusal)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro refusal ⟨carrierPacket, hsame_refl refusal⟩
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
            questionRefusalRoute⟩
      ledger_sound := by
        intro _row source
        exact ⟨provenancePkg, rootPkg, source.right⟩
    }
  exact
    ⟨cert, socketUnary, questionUnary, refusalUnary, readbackUnary, refusalReadUnary,
      rootReadUnary, socketQuestionReadback, questionRefusalRoute, refusalReadRoute,
      rootReadRoute, readbackSameSourceQuestion, provenancePkg, rootPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
