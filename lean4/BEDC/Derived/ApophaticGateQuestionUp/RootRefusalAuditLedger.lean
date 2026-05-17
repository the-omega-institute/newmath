import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_refusal_audit_ledger [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance nameRow bundle pkg →
      Cont readback route rootRead →
        PkgSig bundle rootRead pkg →
          SemanticNameCert
            (fun row : BHist =>
              ApophaticGateQuestionCarrier socket question refusal readback transport route provenance nameRow bundle pkg ∧
                hsame row refusal)
            (fun row : BHist => hsame row refusal ∧ UnaryHistory row ∧ Cont question refusal route)
            (fun _row : BHist =>
              Cont question refusal route ∧ Cont refusal readback transport ∧
                Cont readback route rootRead ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
            hsame ∧
          UnaryHistory refusal ∧ UnaryHistory transport ∧ UnaryHistory rootRead ∧
            Cont question refusal route ∧ Cont refusal readback transport ∧
              Cont readback route rootRead ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackRouteRoot rootPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨_socketUnary, questionUnary, refusalUnary, readbackUnary, transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    questionRefusalRoute, refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteRoot
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          ApophaticGateQuestionCarrier socket question refusal readback transport route provenance nameRow bundle pkg ∧
            hsame row refusal)
        (fun row : BHist => hsame row refusal ∧ UnaryHistory row ∧ Cont question refusal route)
        (fun _row : BHist =>
          Cont question refusal route ∧ Cont refusal readback transport ∧
            Cont readback route rootRead ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle rootRead pkg)
        hsame := by
    constructor
    · constructor
      · exact Exists.intro refusal ⟨carrierPacket, hsame_refl refusal⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact
        ⟨source.right, unary_transport refusalUnary (hsame_symm source.right),
          questionRefusalRoute⟩
    · intro _row _source
      exact
        ⟨questionRefusalRoute, refusalReadbackTransport, readbackRouteRoot,
          provenancePkg, rootPkg⟩
  exact
    ⟨cert, refusalUnary, transportUnary, rootUnary, questionRefusalRoute,
      refusalReadbackTransport, readbackRouteRoot, rootPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
