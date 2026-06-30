import BEDC.Derived.ContextWindowCommitmentUp.NameCertObligations

namespace BEDC.Derived.ContextWindowCommitmentUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContextWindowCommitmentCarrier_nonescape [AskSetup] [PackageSetup]
    {scope prompt boundary refusal consumer transport routes provenance nameCert publicRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory scope →
      UnaryHistory prompt →
        UnaryHistory refusal →
          UnaryHistory routes →
          Cont scope prompt boundary →
            Cont boundary refusal consumer →
              Cont consumer routes publicRead →
                PkgSig bundle provenance pkg →
                  PkgSig bundle nameCert pkg →
                    PkgSig bundle publicRead pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row scope ∨ hsame row prompt ∨ hsame row boundary ∨
                              hsame row refusal ∨ hsame row consumer ∨
                                hsame row transport ∨ hsame row routes ∨
                                  hsame row provenance ∨ hsame row nameCert ∨
                                    hsame row publicRead)
                          (fun row : BHist =>
                            hsame row publicRead ∧ PkgSig bundle publicRead pkg)
                          hsame ∧
                        UnaryHistory boundary ∧ UnaryHistory consumer ∧
                          UnaryHistory publicRead ∧ Cont scope prompt boundary ∧
                            Cont boundary refusal consumer ∧ Cont consumer routes publicRead ∧
                              PkgSig bundle provenance pkg ∧ PkgSig bundle nameCert pkg ∧
                                PkgSig bundle publicRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro scopeUnary promptUnary refusalUnary routesUnary boundaryRoute consumerRoute publicRoute
    provenancePkg namePkg publicPkg
  have boundaryUnary : UnaryHistory boundary :=
    unary_cont_closed scopeUnary promptUnary boundaryRoute
  have consumerUnary : UnaryHistory consumer :=
    unary_cont_closed boundaryUnary refusalUnary consumerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed consumerUnary routesUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row scope ∨ hsame row prompt ∨ hsame row boundary ∨
              hsame row refusal ∨ hsame row consumer ∨ hsame row transport ∨
                hsame row routes ∨ hsame row provenance ∨ hsame row nameCert ∨
                  hsame row publicRead)
          (fun row : BHist => hsame row publicRead ∧ PkgSig bundle publicRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead
        (And.intro (hsame_refl publicRead) publicUnary)
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
          And.intro (hsame_trans (hsame_symm sameRows) source.left)
            (unary_transport source.right sameRows)
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left publicPkg
  }
  exact
    ⟨cert, boundaryUnary, consumerUnary, publicUnary, boundaryRoute, consumerRoute,
      publicRoute, provenancePkg, namePkg, publicPkg⟩

end BEDC.Derived.ContextWindowCommitmentUp
