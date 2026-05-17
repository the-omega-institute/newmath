import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_axiom_purity_consumer_boundary
    [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow purityRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg ->
      Cont refusal readback purityRead ->
        PkgSig bundle purityRead pkg ->
          SemanticNameCert
            (fun row : BHist =>
              ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg ∧ hsame row refusal ∧
                  Cont refusal readback purityRead)
            (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
            (fun row : BHist =>
              PkgSig bundle provenance pkg ∧ PkgSig bundle purityRead pkg ∧
                hsame row refusal ∧ hsame readback (append socket question))
            hsame ∧ UnaryHistory refusal ∧ UnaryHistory readback ∧
              UnaryHistory purityRead ∧ Cont refusal readback purityRead ∧
                hsame readback (append socket question) ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle purityRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier refusalReadbackPurity purityReadPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, _questionUnary, refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSocketQuestion, provenancePkg⟩ := carrier
  have purityReadUnary : UnaryHistory purityRead :=
    unary_cont_closed refusalUnary readbackUnary refusalReadbackPurity
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticGateQuestionCarrier socket question refusal readback transport route
            provenance nameRow bundle pkg ∧ hsame row refusal ∧
              Cont refusal readback purityRead)
        (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
        (fun row : BHist =>
          PkgSig bundle provenance pkg ∧ PkgSig bundle purityRead pkg ∧
            hsame row refusal ∧ hsame readback (append socket question))
        hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro refusal ⟨carrierPacket, hsame_refl refusal, refusalReadbackPurity⟩
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
          exact
            ⟨source.left, hsame_trans (hsame_symm same) source.right.left,
              source.right.right⟩
      }
      pattern_sound := by
        intro _row source
        exact
          ⟨source.right.left,
            unary_transport refusalUnary (hsame_symm source.right.left)⟩
      ledger_sound := by
        intro _row source
        exact
          ⟨provenancePkg, purityReadPkg, source.right.left,
            readbackSameSocketQuestion⟩
    }
  exact
    ⟨cert, refusalUnary, readbackUnary, purityReadUnary, refusalReadbackPurity,
      readbackSameSocketQuestion, provenancePkg, purityReadPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
