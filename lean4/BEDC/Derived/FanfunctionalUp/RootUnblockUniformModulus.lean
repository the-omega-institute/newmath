import BEDC.Derived.FanfunctionalUp.RootUnblockCompactRoute

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootUnblockUniformModulus [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      compactRead uniformRead modulusRead named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport
        replay provenance localName bundle pkg ->
      Cont cantor fan compactRead ->
        Cont compactRead tolerance uniformRead ->
          Cont witness modulus modulusRead ->
            Cont modulusRead localName named ->
              PkgSig bundle modulusRead pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row named ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨
                        hsame row witness ∨ hsame row modulus ∨ hsame row modulusRead ∨
                          hsame row named)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont cantor fan compactRead ∧
                        Cont compactRead tolerance uniformRead ∧
                          Cont witness modulus modulusRead ∧
                            Cont modulusRead localName named ∧
                              PkgSig bundle provenance pkg ∧
                                PkgSig bundle modulusRead pkg)
                    hsame ∧ UnaryHistory compactRead ∧ UnaryHistory uniformRead ∧
                  UnaryHistory modulusRead ∧ UnaryHistory named ∧
                    PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier cantorFanCompact compactToleranceUniform witnessModulusRead
    modulusLocalNameRoute modulusPkg
  obtain ⟨cantorUnary, fanUnary, toleranceUnary, _branchUnary, _depthUnary, witnessUnary,
    modulusUnary, _transportUnary, _replayUnary, provenanceUnary, localNameUnary,
    _transportLocalName, _carrierBranchDepthWitness, _carrierWitnessModulusReplay,
    provenancePkg⟩ := carrier
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed cantorUnary fanUnary cantorFanCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary toleranceUnary compactToleranceUniform
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary modulusUnary witnessModulusRead
  have namedUnary : UnaryHistory named :=
    unary_cont_closed modulusReadUnary localNameUnary modulusLocalNameRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row named ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨
              hsame row witness ∨ hsame row modulus ∨ hsame row modulusRead ∨
                hsame row named)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cantor fan compactRead ∧
              Cont compactRead tolerance uniformRead ∧ Cont witness modulus modulusRead ∧
                Cont modulusRead localName named ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle modulusRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro named ⟨hsame_refl named, namedUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cantorFanCompact, compactToleranceUniform, witnessModulusRead,
          modulusLocalNameRoute, provenancePkg, modulusPkg⟩
  }
  exact ⟨cert, compactUnary, uniformUnary, modulusReadUnary, namedUnary, provenancePkg⟩

end BEDC.Derived.FanfunctionalUp
