import BEDC.Derived.FanfunctionalUp.RootUnblockFanDepth
import BEDC.Derived.FanfunctionalUp.RootUniformModulusObligation

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootUnblockWitnessWindowTotality [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      prefixRead barRead fanDepthRead compactRead uniformRead modulusRead witnessWindow :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg ->
      Cont cantor fan prefixRead ->
        Cont branch depth barRead ->
          Cont barRead fan fanDepthRead ->
            Cont cantor fan compactRead ->
              Cont compactRead tolerance uniformRead ->
                Cont witness modulus modulusRead ->
                  Cont prefixRead modulus witnessWindow ->
                    PkgSig bundle fanDepthRead pkg ->
                      PkgSig bundle modulusRead pkg ->
                        PkgSig bundle witnessWindow pkg ->
                          UnaryHistory witnessWindow ∧
                            SemanticNameCert
                              (fun row : BHist => hsame row witnessWindow ∧ UnaryHistory row)
                              (fun row : BHist =>
                                hsame row cantor ∨ hsame row fan ∨ hsame row prefixRead ∨
                                  hsame row modulus ∨ hsame row witnessWindow)
                              (fun row : BHist =>
                                UnaryHistory row ∧ Cont prefixRead modulus witnessWindow ∧
                                  PkgSig bundle witnessWindow pkg)
                              hsame := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier cantorFanPrefix branchDepthBar barFanDepth cantorFanCompact
    compactToleranceUniform witnessModulusRead prefixModulusWindow fanDepthPkg modulusPkg
    witnessWindowPkg
  obtain ⟨cantorUnary, fanUnary, toleranceUnary, branchUnary, depthUnary, witnessUnary,
    modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _provenancePkg⟩ := carrier
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
  have witnessWindowUnary : UnaryHistory witnessWindow :=
    unary_cont_closed prefixUnary modulusUnary prefixModulusWindow
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row witnessWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row fan ∨ hsame row prefixRead ∨
              hsame row modulus ∨ hsame row witnessWindow)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont prefixRead modulus witnessWindow ∧
              PkgSig bundle witnessWindow pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro witnessWindow ⟨hsame_refl witnessWindow, witnessWindowUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, prefixModulusWindow, witnessWindowPkg⟩
  }
  exact ⟨witnessWindowUnary, cert⟩

end BEDC.Derived.FanfunctionalUp
