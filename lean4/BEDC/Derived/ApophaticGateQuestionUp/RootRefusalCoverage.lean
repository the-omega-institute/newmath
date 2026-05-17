import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_refusal_coverage [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow rootRead refusalRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg ->
      Cont readback route rootRead ->
        Cont refusal readback refusalRead ->
          PkgSig bundle rootRead pkg ->
            PkgSig bundle refusalRead pkg ->
              SemanticNameCert
                  (fun row : BHist =>
                    ApophaticGateQuestionCarrier socket question refusal readback transport route
                      provenance nameRow bundle pkg ∧ hsame row refusal)
                  (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
                  (fun row : BHist =>
                    PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg ∧
                      hsame row refusal ∧ Cont refusal readback refusalRead)
                  hsame ∧
                UnaryHistory socket ∧ UnaryHistory refusal ∧ UnaryHistory readback ∧
                  UnaryHistory rootRead ∧ UnaryHistory refusalRead ∧
                    Cont socket question readback ∧ Cont refusal readback refusalRead ∧
                      PkgSig bundle rootRead pkg ∧ PkgSig bundle refusalRead pkg := by
  -- BEDC touchpoint anchor: BHist AskSetup PackageSetup ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier readbackRouteRoot refusalReadbackRoute rootPkg refusalPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, _questionUnary, refusalUnary, readbackUnary, _transportUnary,
    routeUnary, _provenanceUnary, _nameRowUnary, socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed readbackUnary routeUnary readbackRouteRoot
  have refusalReadUnary : UnaryHistory refusalRead :=
    unary_cont_closed refusalUnary readbackUnary refusalReadbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
              provenance nameRow bundle pkg ∧ hsame row refusal)
          (fun row : BHist => hsame row refusal ∧ UnaryHistory row)
          (fun row : BHist =>
            PkgSig bundle provenance pkg ∧ PkgSig bundle refusalRead pkg ∧
              hsame row refusal ∧ Cont refusal readback refusalRead)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro refusal ⟨carrierPacket, hsame_refl refusal⟩
      · intro row _source
        exact hsame_refl row
      · intro row row' same
        exact hsame_symm same
      · intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro row row' same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro row source
      exact ⟨source.right, unary_transport refusalUnary (hsame_symm source.right)⟩
    · intro row source
      exact ⟨provenancePkg, refusalPkg, source.right, refusalReadbackRoute⟩
  exact
    ⟨cert, socketUnary, refusalUnary, readbackUnary, rootUnary, refusalReadUnary,
      socketQuestionReadback, refusalReadbackRoute, rootPkg, refusalPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
