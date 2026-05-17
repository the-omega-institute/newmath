import BEDC.Derived.ApophaticGateQuestionUp

namespace BEDC.Derived.ApophaticGateQuestionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ApophaticGateQuestionCarrier_root_source_exactness [AskSetup] [PackageSetup]
    {socket question refusal readback transport route provenance nameRow sourceRead rootRead :
      BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ApophaticGateQuestionCarrier socket question refusal readback transport route provenance
        nameRow bundle pkg →
      Cont socket question sourceRead →
        Cont sourceRead readback rootRead →
          PkgSig bundle rootRead pkg →
            SemanticNameCert
                (fun row : BHist =>
                  ApophaticGateQuestionCarrier socket question refusal readback transport route
                      provenance nameRow bundle pkg ∧
                    hsame row sourceRead)
                (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
                (fun _row : BHist =>
                  Cont socket question sourceRead ∧ Cont sourceRead readback rootRead ∧
                    PkgSig bundle provenance pkg)
                hsame ∧
              UnaryHistory socket ∧ UnaryHistory question ∧ UnaryHistory sourceRead ∧
                UnaryHistory rootRead ∧ Cont socket question sourceRead ∧
                  Cont sourceRead readback rootRead ∧ PkgSig bundle rootRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame Cont
  intro carrier socketQuestionSource sourceReadbackRoot rootPkg
  have carrierPacket :
      ApophaticGateQuestionCarrier socket question refusal readback transport route
        provenance nameRow bundle pkg :=
    carrier
  obtain ⟨socketUnary, questionUnary, _refusalUnary, readbackUnary, _transportUnary,
    _routeUnary, _provenanceUnary, _nameRowUnary, _socketQuestionReadback,
    _questionRefusalRoute, _refusalReadbackTransport, _readbackRouteNameRow,
    _readbackSameSourceQuestion, provenancePkg⟩ := carrier
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed socketUnary questionUnary socketQuestionSource
  have rootReadUnary : UnaryHistory rootRead :=
    unary_cont_closed sourceReadUnary readbackUnary sourceReadbackRoot
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            ApophaticGateQuestionCarrier socket question refusal readback transport route
                provenance nameRow bundle pkg ∧
              hsame row sourceRead)
          (fun row : BHist => hsame row sourceRead ∧ UnaryHistory row)
          (fun _row : BHist =>
            Cont socket question sourceRead ∧ Cont sourceRead readback rootRead ∧
              PkgSig bundle provenance pkg)
          hsame := by
    constructor
    · constructor
      · exact Exists.intro sourceRead ⟨carrierPacket, hsame_refl sourceRead⟩
      · intro row _source
        exact hsame_refl row
      · intro _row _other same
        exact hsame_symm same
      · intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      · intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    · intro _row source
      exact ⟨source.right, unary_transport sourceReadUnary (hsame_symm source.right)⟩
    · intro _row _source
      exact ⟨socketQuestionSource, sourceReadbackRoot, provenancePkg⟩
  exact
    ⟨cert, socketUnary, questionUnary, sourceReadUnary, rootReadUnary,
      socketQuestionSource, sourceReadbackRoot, rootPkg⟩

end BEDC.Derived.ApophaticGateQuestionUp
