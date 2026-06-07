import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootUnblockCompactRoute [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      prefixRead barRead fanDepthRead compactRead uniformRead modulusRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg ->
      Cont cantor fan prefixRead ->
        Cont branch depth barRead ->
          Cont barRead fan fanDepthRead ->
            Cont cantor fan compactRead ->
              Cont compactRead tolerance uniformRead ->
                Cont witness modulus modulusRead ->
                  PkgSig bundle fanDepthRead pkg ->
                    PkgSig bundle modulusRead pkg ->
                      SemanticNameCert
                            (fun row : BHist =>
                              hsame row modulusRead ∧ UnaryHistory row ∧
                                PkgSig bundle row pkg)
                            (fun row : BHist =>
                              hsame row cantor ∨ hsame row fan ∨ hsame row branch ∨
                                hsame row depth ∨ hsame row witness ∨ hsame row modulus ∨
                                  hsame row modulusRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont cantor fan compactRead ∧
                                Cont compactRead tolerance uniformRead ∧
                                  Cont witness modulus modulusRead ∧
                                    PkgSig bundle modulusRead pkg)
                            hsame ∧
                        UnaryHistory prefixRead ∧ UnaryHistory barRead ∧
                          UnaryHistory fanDepthRead ∧ UnaryHistory compactRead ∧
                            UnaryHistory uniformRead ∧ UnaryHistory modulusRead ∧
                              PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier cantorFanPrefix branchDepthBar barFanDepth cantorFanCompact
    compactToleranceUniform witnessModulusRead fanDepthPkg modulusPkg
  obtain ⟨cantorUnary, fanUnary, toleranceUnary, branchUnary, depthUnary, witnessUnary,
    modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportLocalName, _carrierBranchDepthWitness, _carrierWitnessModulusReplay,
    provenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cantorUnary fanUnary cantorFanPrefix
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed branchUnary depthUnary branchDepthBar
  have fanDepthUnary : UnaryHistory fanDepthRead :=
    unary_cont_closed barUnary fanUnary barFanDepth
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed cantorUnary fanUnary cantorFanCompact
  have uniformUnary : UnaryHistory uniformRead :=
    unary_cont_closed compactUnary toleranceUnary compactToleranceUniform
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary modulusUnary witnessModulusRead
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row modulusRead ∧ UnaryHistory row ∧ PkgSig bundle row pkg)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row branch ∨ hsame row depth ∨
              hsame row witness ∨ hsame row modulus ∨ hsame row modulusRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cantor fan compactRead ∧
              Cont compactRead tolerance uniformRead ∧ Cont witness modulus modulusRead ∧
                PkgSig bundle modulusRead pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro modulusRead
          ⟨hsame_refl modulusRead, modulusReadUnary, modulusPkg⟩
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
      intro _row source
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right.left, cantorFanCompact, compactToleranceUniform, witnessModulusRead,
          modulusPkg⟩
  }
  exact
    ⟨cert, prefixUnary, barUnary, fanDepthUnary, compactUnary, uniformUnary, modulusReadUnary,
      provenancePkg⟩

end BEDC.Derived.FanfunctionalUp
