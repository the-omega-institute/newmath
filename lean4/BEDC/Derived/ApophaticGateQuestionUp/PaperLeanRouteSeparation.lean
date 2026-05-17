import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_paper_lean_route_separation [AskSetup]
    [PackageSetup]
    {socket question refusal readback transport route provenance nameRow paperRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont readback route paperRead →
        PkgSig bundle paperRead pkg →
          SemanticNameCert
              (fun row : BHist =>
                ApophaticGateQuestionCarrier socket question refusal readback transport
                  route provenance nameRow bundle pkg ∧ hsame row readback)
              (fun row : BHist => hsame row readback ∧ UnaryHistory row)
              (fun _row : BHist =>
                Cont socket question readback ∧ Cont readback route paperRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle paperRead pkg)
              hsame ∧
            UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory readback ∧
              UnaryHistory paperRead ∧ Cont socket question readback ∧
                Cont readback route paperRead ∧ hsame readback (append socket question) ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle paperRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier paperRoute paperPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    readbackSameSocketQuestion, provenancePkg⟩ := carrier
  have paperUnary : UnaryHistory paperRead :=
    unary_cont_closed readbackUnary routeUnary paperRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row readback)
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket question readback ∧ Cont readback route paperRead ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle paperRead pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro readback ⟨carrierPacket, hsame_refl readback⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport readbackUnary (hsame_symm source.right)⟩
    · intro _row _source
      exact ⟨socketQuestionReadback, paperRoute, provenancePkg, paperPkg⟩
  exact
    ⟨cert, socketUnary, questionUnary, readbackUnary, paperUnary,
      socketQuestionReadback, paperRoute, readbackSameSocketQuestion, provenancePkg,
      paperPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
