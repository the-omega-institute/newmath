import BEDC.Derived.FanfunctionalUp.RootWindowObligations

namespace BEDC.Derived.FanfunctionalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FanFunctionalRootCantorWindowHandoff [AskSetup] [PackageSetup]
    {cantor fan tolerance branch depth witness modulus transport replay provenance
      localName prefixRead barRead windowRead namedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    FanFunctionalCarrierSurface cantor fan tolerance branch depth witness modulus transport
        replay provenance localName bundle pkg →
      Cont cantor branch prefixRead →
        Cont prefixRead witness windowRead →
          Cont windowRead depth barRead →
            Cont barRead localName namedRead →
              PkgSig bundle provenance pkg →
                PkgSig bundle namedRead pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row cantor ∨ hsame row branch ∨ hsame row witness ∨
                          hsame row depth ∨ hsame row barRead ∨ hsame row namedRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont cantor branch prefixRead ∧
                          Cont prefixRead witness windowRead ∧
                            Cont windowRead depth barRead ∧
                              Cont barRead localName namedRead ∧
                                PkgSig bundle provenance pkg ∧
                                  PkgSig bundle namedRead pkg)
                      hsame ∧ UnaryHistory prefixRead ∧ UnaryHistory windowRead ∧
                    UnaryHistory barRead ∧ UnaryHistory namedRead := by
  -- BEDC touchpoint anchor: FanFunctionalCarrierSurface BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro carrier cantorBranchPrefix prefixWitnessWindow windowDepthBar barLocalNameNamed
    provenancePkg namedPkg
  obtain ⟨cantorUnary, _fanUnary, _toleranceUnary, branchUnary, depthUnary,
    witnessUnary, _modulusUnary, _transportUnary, _replayUnary, _provenanceUnary,
    localNameUnary, _transportLocalName, _branchDepthWitness, _witnessModulusReplay,
    _carrierProvenancePkg⟩ := carrier
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed cantorUnary branchUnary cantorBranchPrefix
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed prefixUnary witnessUnary prefixWitnessWindow
  have barUnary : UnaryHistory barRead :=
    unary_cont_closed windowUnary depthUnary windowDepthBar
  have namedUnary : UnaryHistory namedRead :=
    unary_cont_closed barUnary localNameUnary barLocalNameNamed
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row namedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row cantor ∨ hsame row branch ∨ hsame row witness ∨ hsame row depth ∨
              hsame row barRead ∨ hsame row namedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont cantor branch prefixRead ∧
              Cont prefixRead witness windowRead ∧ Cont windowRead depth barRead ∧
                Cont barRead localName namedRead ∧ PkgSig bundle provenance pkg ∧
                  PkgSig bundle namedRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro namedRead ⟨hsame_refl namedRead, namedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cantorBranchPrefix, prefixWitnessWindow, windowDepthBar,
          barLocalNameNamed, provenancePkg, namedPkg⟩
  }
  exact ⟨cert, prefixUnary, windowUnary, barUnary, namedUnary⟩

end BEDC.Derived.FanfunctionalUp
