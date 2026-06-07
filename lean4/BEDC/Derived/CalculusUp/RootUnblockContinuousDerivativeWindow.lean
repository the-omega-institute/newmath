import BEDC.Derived.CalculusUp.RootUnblockLimitWindowScope

namespace BEDC.Derived.CalculusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CalculusRootUnblockContinuousDerivativeWindow [AskSetup] [PackageSetup]
    {graphRow derivativeRow toleranceRow readbackRow realSeal transport replay provenance
      localName graphRead derivativeRead toleranceRead readbackRead sealRead
      structuralRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory graphRow ->
      UnaryHistory derivativeRow ->
        UnaryHistory toleranceRow ->
          UnaryHistory readbackRow ->
            UnaryHistory realSeal ->
              UnaryHistory transport ->
                UnaryHistory replay ->
                  Cont graphRow derivativeRow derivativeRead ->
                    Cont derivativeRead toleranceRow toleranceRead ->
                      Cont toleranceRead readbackRow readbackRead ->
                        Cont readbackRead realSeal sealRead ->
                          Cont transport replay structuralRead ->
                            PkgSig bundle provenance pkg ->
                              PkgSig bundle localName pkg ->
                                SemanticNameCert
                                    (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row graphRow ∨ hsame row derivativeRow ∨
                                        hsame row toleranceRow ∨ hsame row readbackRow ∨
                                          hsame row realSeal ∨ hsame row sealRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧
                                        Cont graphRow derivativeRow derivativeRead ∧
                                          Cont derivativeRead toleranceRow toleranceRead ∧
                                            Cont toleranceRead readbackRow readbackRead ∧
                                              Cont readbackRead realSeal sealRead ∧
                                                PkgSig bundle provenance pkg ∧
                                                  PkgSig bundle localName pkg)
                                    hsame ∧
                                  UnaryHistory derivativeRead ∧
                                    UnaryHistory toleranceRead ∧
                                      UnaryHistory readbackRead ∧
                                        UnaryHistory sealRead ∧
                                          UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro graphUnary derivativeUnary toleranceUnary readbackUnary realUnary transportUnary
    replayUnary derivativeRoute toleranceRoute readbackRoute sealRoute structuralRoute
    provenancePkg localNamePkg
  have derivativeReadUnary : UnaryHistory derivativeRead :=
    unary_cont_closed graphUnary derivativeUnary derivativeRoute
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed derivativeReadUnary toleranceUnary toleranceRoute
  have readbackReadUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceReadUnary readbackUnary readbackRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackReadUnary realUnary sealRoute
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed transportUnary replayUnary structuralRoute
  constructor
  · exact {
      core := {
        carrier_inhabited := Exists.intro sealRead ⟨hsame_refl sealRead, sealReadUnary⟩
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
          ⟨source.right, derivativeRoute, toleranceRoute, readbackRoute, sealRoute,
            provenancePkg, localNamePkg⟩
    }
  · exact
      ⟨derivativeReadUnary, toleranceReadUnary, readbackReadUnary, sealReadUnary,
        structuralReadUnary⟩

end BEDC.Derived.CalculusUp
