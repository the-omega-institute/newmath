import BEDC.Derived.RegularCauchyWitnessSelectorUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RegularCauchyWitnessSelectorUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyWitnessSelectorNameCertSurface [AskSetup] [PackageSetup]
    {M W T R E H C P N sourceRead terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory M ->
      UnaryHistory W ->
        UnaryHistory T ->
          UnaryHistory R ->
            UnaryHistory E ->
              Cont M W sourceRead ->
                Cont sourceRead T R ->
                  Cont R E terminalRead ->
                    PkgSig bundle N pkg ->
                      PkgSig bundle terminalRead pkg ->
                        regularCauchyWitnessSelectorToEventFlow
                            (RegularCauchyWitnessSelectorUp.mk M W T R E H C P N) =
                              [regularCauchyWitnessSelectorEncodeBHist M,
                                regularCauchyWitnessSelectorEncodeBHist W,
                                regularCauchyWitnessSelectorEncodeBHist T,
                                regularCauchyWitnessSelectorEncodeBHist R,
                                regularCauchyWitnessSelectorEncodeBHist E,
                                regularCauchyWitnessSelectorEncodeBHist H,
                                regularCauchyWitnessSelectorEncodeBHist C,
                                regularCauchyWitnessSelectorEncodeBHist P,
                                regularCauchyWitnessSelectorEncodeBHist N] ∧
                          UnaryHistory sourceRead ∧
                            UnaryHistory terminalRead ∧
                              SemanticNameCert
                                (fun row : BHist => hsame row terminalRead ∧
                                  UnaryHistory row)
                                (fun row : BHist =>
                                  hsame row sourceRead ∨ hsame row R ∨
                                    hsame row terminalRead)
                                (fun row : BHist =>
                                  hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
                                hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro mUnary wUnary tUnary rUnary eUnary modulusWindow sourceTolerance routeTerminal
    _namePkg terminalPkg
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed mUnary wUnary modulusWindow
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed rUnary eUnary routeTerminal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row sourceRead ∨ hsame row R ∨ hsame row terminalRead)
        (fun row : BHist =>
          hsame row terminalRead ∧ PkgSig bundle terminalRead pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro terminalRead ⟨hsame_refl terminalRead, terminalUnary⟩
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.left, terminalPkg⟩
  }
  exact ⟨rfl, sourceUnary, terminalUnary, cert⟩

end BEDC.Derived.RegularCauchyWitnessSelectorUp
