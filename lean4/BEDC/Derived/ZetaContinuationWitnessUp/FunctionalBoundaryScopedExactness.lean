import BEDC.Derived.ZetaContinuationWitnessUp

namespace BEDC.Derived.ZetaContinuationWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ZetaContinuationWitnessFunctionalBoundaryScopedExactness [AskSetup] [PackageSetup]
    {basic eta analytic pole functional zeroLedger gamma transports routes provenance name etaPrime
      analyticPrime transportsPrime zeroLedgerPrime gammaPrime functionalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    ZetaContinuationWitnessPacket basic eta analytic pole functional zeroLedger gamma transports
      routes provenance name bundle pkg →
    Cont basic etaPrime analyticPrime →
    Cont analyticPrime functional transportsPrime →
    Cont pole zeroLedgerPrime gammaPrime →
    hsame eta etaPrime →
    hsame zeroLedger zeroLedgerPrime →
    UnaryHistory routes →
    UnaryHistory name →
    Cont routes name functionalRead →
    PkgSig bundle functionalRead pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row pole ∨ hsame row functional ∨ hsame row gamma ∨ hsame row functionalRead)
          (fun row : BHist =>
            hsame row pole ∨ hsame row functional ∨ hsame row gamma ∨ hsame row functionalRead)
          (fun _row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle functionalRead pkg)
          hsame ∧
        hsame analytic analyticPrime ∧ hsame transports transportsPrime ∧
          hsame gamma gammaPrime ∧ UnaryHistory functionalRead ∧
            hsame functionalRead (append routes name) := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro packet basicRoute functionalRoute gammaRoute etaSame zeroLedgerSame routesUnary
    nameUnary routesNameFunctional functionalReadPkg
  obtain ⟨basicEtaAnalytic, analyticFunctionalTransports, poleZeroLedgerGamma,
    _transportProvenance, namePkg, provenancePkg⟩ := packet
  have analyticSame : hsame analytic analyticPrime :=
    cont_respects_hsame (hsame_refl basic) etaSame basicEtaAnalytic basicRoute
  have transportsSame : hsame transports transportsPrime :=
    cont_respects_hsame analyticSame (hsame_refl functional) analyticFunctionalTransports
      functionalRoute
  have gammaSame : hsame gamma gammaPrime :=
    cont_respects_hsame (hsame_refl pole) zeroLedgerSame poleZeroLedgerGamma gammaRoute
  have functionalReadUnary : UnaryHistory functionalRead :=
    unary_cont_closed routesUnary nameUnary routesNameFunctional
  have sourcePole :
      (fun row : BHist =>
        hsame row pole ∨ hsame row functional ∨ hsame row gamma ∨ hsame row functionalRead)
        pole := by
    exact Or.inl (hsame_refl pole)
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row pole ∨ hsame row functional ∨ hsame row gamma ∨ hsame row functionalRead)
          (fun row : BHist =>
            hsame row pole ∨ hsame row functional ∨ hsame row gamma ∨ hsame row functionalRead)
          (fun _row : BHist =>
            PkgSig bundle name pkg ∧ PkgSig bundle provenance pkg ∧
              PkgSig bundle functionalRead pkg)
          hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro pole sourcePole
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
          intro row other sameRows source
          have moveToOther :
              hsame other pole ∨ hsame other functional ∨ hsame other gamma ∨
                hsame other functionalRead := by
            cases source with
            | inl rowPole =>
                exact Or.inl (hsame_trans (hsame_symm sameRows) rowPole)
            | inr rest =>
                cases rest with
                | inl rowFunctional =>
                    exact Or.inr
                      (Or.inl (hsame_trans (hsame_symm sameRows) rowFunctional))
                | inr rest' =>
                    cases rest' with
                    | inl rowGamma =>
                        exact Or.inr
                          (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) rowGamma)))
                    | inr rowFunctionalRead =>
                        exact Or.inr
                          (Or.inr
                            (Or.inr
                              (hsame_trans (hsame_symm sameRows) rowFunctionalRead)))
          exact moveToOther
      }
      pattern_sound := by
        intro _row source
        exact source
      ledger_sound := by
        intro _row _source
        exact ⟨namePkg, provenancePkg, functionalReadPkg⟩
    }
  exact
    ⟨cert, analyticSame, transportsSame, gammaSame, functionalReadUnary,
      routesNameFunctional⟩

end BEDC.Derived.ZetaContinuationWitnessUp
