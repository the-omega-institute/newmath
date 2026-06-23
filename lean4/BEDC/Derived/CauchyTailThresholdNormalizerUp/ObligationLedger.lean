import BEDC.Derived.CauchyTailThresholdNormalizerUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailThresholdNormalizerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyTailThresholdNormalizerObligationLedger [AskSetup] [PackageSetup]
    {S M Theta W0 W1 D R A E H C P L N terminalRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory M →
        UnaryHistory Theta →
          UnaryHistory W0 →
            UnaryHistory W1 →
              UnaryHistory D →
                UnaryHistory R →
                  UnaryHistory A →
                    UnaryHistory E →
                      UnaryHistory C →
                        Cont S M Theta →
                          Cont Theta W0 W1 →
                            Cont W1 D R →
                              Cont R A E →
                                Cont E C terminalRead →
                                  PkgSig bundle P pkg →
                                    SemanticNameCert
                                        (fun row : BHist => hsame row terminalRead ∧
                                          UnaryHistory row)
                                        (fun row : BHist =>
                                          hsame row S ∨ hsame row M ∨ hsame row Theta ∨
                                            hsame row W0 ∨ hsame row W1 ∨ hsame row D ∨
                                              hsame row R ∨ hsame row A ∨ hsame row E ∨
                                                hsame row H ∨ hsame row C ∨ hsame row P ∨
                                                  hsame row L ∨ hsame row N ∨
                                                    hsame row terminalRead)
                                        (fun row : BHist =>
                                          UnaryHistory row ∧ Cont S M Theta ∧
                                            Cont Theta W0 W1 ∧ Cont W1 D R ∧
                                              Cont R A E ∧ Cont E C terminalRead ∧
                                                PkgSig bundle P pkg)
                                        hsame ∧
                                      UnaryHistory terminalRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sUnary mUnary _thetaUnary w0Unary w1Unary dUnary rUnary aUnary eUnary cUnary
    sourceRoute thresholdRoute readbackRoute agreementRoute terminalRoute provenancePkg
  have terminalUnary : UnaryHistory terminalRead :=
    unary_cont_closed eUnary cUnary terminalRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row terminalRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨ hsame row W1 ∨
              hsame row D ∨ hsame row R ∨ hsame row A ∨ hsame row E ∨ hsame row H ∨
                hsame row C ∨ hsame row P ∨ hsame row L ∨ hsame row N ∨
                  hsame row terminalRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S M Theta ∧ Cont Theta W0 W1 ∧ Cont W1 D R ∧
              Cont R A E ∧ Cont E C terminalRead ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro terminalRead
        ⟨hsame_refl terminalRead, terminalUnary⟩
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
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      right
      exact source.left
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, sourceRoute, thresholdRoute, readbackRoute, agreementRoute,
          terminalRoute, provenancePkg⟩
  }
  exact ⟨cert, terminalUnary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
