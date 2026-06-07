import BEDC.Derived.FanfunctionalUp.NameCertObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalModulusWindowMonotonicity [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance localName
      prefixRead barRead modulusRead strongerRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport replay
        provenance localName bundle pkg ->
      Cont cantor fan prefixRead ->
        Cont prefixRead depth barRead ->
          Cont witness modulus modulusRead ->
            Cont modulusRead tolerance strongerRead ->
              PkgSig bundle strongerRead pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row strongerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row cantor ∨ hsame row fan ∨ hsame row depth ∨
                      hsame row witness ∨ hsame row modulus ∨ hsame row modulusRead ∨
                        hsame row tolerance ∨ hsame row strongerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont cantor fan prefixRead ∧
                      Cont prefixRead depth barRead ∧ Cont witness modulus modulusRead ∧
                        Cont modulusRead tolerance strongerRead ∧
                          PkgSig bundle strongerRead pkg)
                  hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory barRead ∧
                    UnaryHistory modulusRead ∧ UnaryHistory strongerRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier cantorFanPrefix prefixDepthBar witnessModulusRead modulusToleranceStronger
    strongerPkg
  obtain ⟨cantorUnary, fanUnary, toleranceUnary, _branchUnary, depthUnary, witnessUnary,
    modulusUnary, _transportUnary, _replayUnary, _provenanceUnary, _localNameUnary,
    _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _provenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cantorUnary fanUnary cantorFanPrefix
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed prefixUnary depthUnary prefixDepthBar
  have modulusReadUnary : UnaryHistory modulusRead :=
    unary_cont_closed witnessUnary modulusUnary witnessModulusRead
  have strongerUnary : UnaryHistory strongerRead :=
    unary_cont_closed modulusReadUnary toleranceUnary modulusToleranceStronger
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row strongerRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row cantor ∨ hsame row fan ∨ hsame row depth ∨ hsame row witness ∨
            hsame row modulus ∨ hsame row modulusRead ∨ hsame row tolerance ∨
              hsame row strongerRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont cantor fan prefixRead ∧ Cont prefixRead depth barRead ∧
            Cont witness modulus modulusRead ∧ Cont modulusRead tolerance strongerRead ∧
              PkgSig bundle strongerRead pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro strongerRead
        ⟨hsame_refl strongerRead, strongerUnary⟩
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
        intro _row _other sameRows sourceRow
        exact
          ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
            unary_transport sourceRow.right sameRows⟩
    }
    pattern_sound := by
      intro _row sourceRow
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr sourceRow.left))))))
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, cantorFanPrefix, prefixDepthBar, witnessModulusRead,
          modulusToleranceStronger, strongerPkg⟩
  }
  exact ⟨cert, prefixUnary, barUnary, modulusReadUnary, strongerUnary⟩

end BEDC.Derived.FanfunctionalUp
