import BEDC.Derived.ContextFreeGrammarUp

namespace BEDC.Derived.ContextFreeGrammarUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ContextFreeGrammarRegularLanguageInclusionCertificate [AskSetup] [PackageSetup]
    {terminal nonterminal start production yield derivation readback transport route provenance name
      transitionRun simulatedRead yieldRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory terminal →
      UnaryHistory production →
        UnaryHistory derivation →
          UnaryHistory readback →
            UnaryHistory yield →
              PkgSig bundle provenance pkg →
                Cont production derivation transitionRun →
                  Cont transitionRun readback simulatedRead →
                    Cont simulatedRead yield yieldRead →
                      PkgSig bundle yieldRead pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row yieldRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row terminal ∨ hsame row production ∨
                                hsame row derivation ∨ hsame row readback ∨
                                  hsame row yield ∨ hsame row yieldRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧
                                Cont production derivation transitionRun ∧
                                  Cont transitionRun readback simulatedRead ∧
                                    Cont simulatedRead yield yieldRead ∧
                                      PkgSig bundle yieldRead pkg)
                            hsame ∧ UnaryHistory transitionRun ∧
                              UnaryHistory simulatedRead ∧ UnaryHistory yieldRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro terminalUnary productionUnary derivationUnary readbackUnary yieldUnary _provenancePkg
    productionDerivation transitionReadback simulatedYield yieldPkg
  have transitionUnary : UnaryHistory transitionRun :=
    unary_cont_closed productionUnary derivationUnary productionDerivation
  have simulatedUnary : UnaryHistory simulatedRead :=
    unary_cont_closed transitionUnary readbackUnary transitionReadback
  have yieldReadUnary : UnaryHistory yieldRead :=
    unary_cont_closed simulatedUnary yieldUnary simulatedYield
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row yieldRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row terminal ∨ hsame row production ∨ hsame row derivation ∨
              hsame row readback ∨ hsame row yield ∨ hsame row yieldRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont production derivation transitionRun ∧
              Cont transitionRun readback simulatedRead ∧
                Cont simulatedRead yield yieldRead ∧ PkgSig bundle yieldRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro yieldRead ⟨hsame_refl yieldRead, yieldReadUnary⟩
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
      exact ⟨source.right, productionDerivation, transitionReadback, simulatedYield, yieldPkg⟩
  }
  exact ⟨cert, transitionUnary, simulatedUnary, yieldReadUnary⟩

end BEDC.Derived.ContextFreeGrammarUp
