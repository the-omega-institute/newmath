import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootCarrierAdmission [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance
      localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport
        replay provenance localName bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨
              hsame row branch ∨ hsame row depth ∨ hsame row witness ∨
                hsame row modulus ∨ hsame row transport ∨ hsame row replay ∨
                  hsame row provenance ∨ hsame row localName)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory cantor ∧ UnaryHistory fan ∧ UnaryHistory tolerance ∧
          UnaryHistory branch ∧ UnaryHistory depth ∧ UnaryHistory witness ∧
            UnaryHistory modulus ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
              UnaryHistory provenance ∧ UnaryHistory localName := by
  -- BEDC touchpoint anchor: BHist ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier
  obtain ⟨cantorUnary, fanUnary, toleranceUnary, branchUnary, depthUnary, witnessUnary,
    modulusUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay, provenancePkg⟩ :=
      carrier
  have rowUnaryOfSource :
      ∀ {row : BHist},
        (hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨ hsame row branch ∨
          hsame row depth ∨ hsame row witness ∨ hsame row modulus ∨
            hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
              hsame row localName) →
          UnaryHistory row := by
    intro row source
    cases source with
    | inl sameCantor =>
        exact unary_transport cantorUnary (hsame_symm sameCantor)
    | inr rest =>
        cases rest with
        | inl sameFan =>
            exact unary_transport fanUnary (hsame_symm sameFan)
        | inr rest =>
            cases rest with
            | inl sameTolerance =>
                exact unary_transport toleranceUnary (hsame_symm sameTolerance)
            | inr rest =>
                cases rest with
                | inl sameBranch =>
                    exact unary_transport branchUnary (hsame_symm sameBranch)
                | inr rest =>
                    cases rest with
                    | inl sameDepth =>
                        exact unary_transport depthUnary (hsame_symm sameDepth)
                    | inr rest =>
                        cases rest with
                        | inl sameWitness =>
                            exact unary_transport witnessUnary (hsame_symm sameWitness)
                        | inr rest =>
                            cases rest with
                            | inl sameModulus =>
                                exact unary_transport modulusUnary (hsame_symm sameModulus)
                            | inr rest =>
                                cases rest with
                                | inl sameTransport =>
                                    exact unary_transport transportUnary
                                      (hsame_symm sameTransport)
                                | inr rest =>
                                    cases rest with
                                    | inl sameReplay =>
                                        exact unary_transport replayUnary
                                          (hsame_symm sameReplay)
                                    | inr rest =>
                                        cases rest with
                                        | inl sameProvenance =>
                                            exact unary_transport provenanceUnary
                                              (hsame_symm sameProvenance)
                                        | inr sameLocalName =>
                                            exact unary_transport localNameUnary
                                              (hsame_symm sameLocalName)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row tolerance ∨ hsame row branch ∨
              hsame row depth ∨ hsame row witness ∨ hsame row modulus ∨
                hsame row transport ∨ hsame row replay ∨ hsame row provenance ∨
                  hsame row localName)
          (fun row : BHist => UnaryHistory row)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro cantor (Or.inl (hsame_refl cantor))
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      exact rowUnaryOfSource source
    ledger_sound := by
      intro row source
      exact ⟨rowUnaryOfSource source, provenancePkg⟩
  }
  exact
    ⟨cert, cantorUnary, fanUnary, toleranceUnary, branchUnary, depthUnary, witnessUnary,
      modulusUnary, transportUnary, replayUnary, provenanceUnary, localNameUnary⟩

end BEDC.Derived.FanfunctionalUp
