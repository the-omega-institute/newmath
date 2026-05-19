import BEDC.Derived.StreamNameUp
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamNameOpenPhaseFourFaceExitReadback [AskSetup] [PackageSetup]
    {window dyadic regseq real support exit terminal readback : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window ->
      UnaryHistory dyadic ->
        UnaryHistory regseq ->
          UnaryHistory real ->
            Cont window dyadic support ->
              Cont regseq real exit ->
                Cont support exit terminal ->
                  Cont terminal support readback ->
                    PkgSig bundle terminal pkg ->
                      PkgSig bundle readback pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row window ∨ hsame row dyadic ∨ hsame row regseq ∨
                                hsame row real ∨ hsame row terminal ∨ hsame row readback)
                            (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
                            hsame ∧
                          UnaryHistory support ∧ UnaryHistory exit ∧ UnaryHistory terminal ∧
                            UnaryHistory readback ∧ Cont window dyadic support ∧
                              Cont regseq real exit ∧ Cont support exit terminal ∧
                                Cont terminal support readback ∧ PkgSig bundle terminal pkg ∧
                                  PkgSig bundle readback pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro windowUnary dyadicUnary regseqUnary realUnary windowDyadicSupport regseqRealExit
    supportExitTerminal terminalSupportReadback terminalPkg readbackPkg
  have supportUnary : UnaryHistory support :=
    unary_cont_closed windowUnary dyadicUnary windowDyadicSupport
  have exitUnary : UnaryHistory exit :=
    unary_cont_closed regseqUnary realUnary regseqRealExit
  have terminalUnary : UnaryHistory terminal :=
    unary_cont_closed supportUnary exitUnary supportExitTerminal
  have readbackUnary : UnaryHistory readback :=
    unary_cont_closed terminalUnary supportUnary terminalSupportReadback
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row window ∨ hsame row dyadic ∨ hsame row regseq ∨
              hsame row real ∨ hsame row terminal ∨ hsame row readback)
          (fun row : BHist => hsame row readback ∧ PkgSig bundle readback pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback
        ⟨hsame_refl readback, readbackUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackPkg⟩
  }
  exact
    ⟨cert, supportUnary, exitUnary, terminalUnary, readbackUnary, windowDyadicSupport,
      regseqRealExit, supportExitTerminal, terminalSupportReadback, terminalPkg, readbackPkg⟩

end BEDC.Derived.StreamNameUp
