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

theorem CauchyTailThresholdNormalizerRealSealHandoff [AskSetup] [PackageSetup]
    {S M Theta W0 W1 D R A E H C P L N sourceRead sealRead windowRead toleranceRead
      agreementRead realRead structuralRead : BHist}
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
                      UnaryHistory H →
                        Cont S M sourceRead →
                          Cont sourceRead Theta sealRead →
                            Cont sealRead W0 windowRead →
                              Cont windowRead W1 toleranceRead →
                                Cont toleranceRead D R →
                                  Cont R A agreementRead →
                                    Cont agreementRead E realRead →
                                      Cont realRead H structuralRead →
                                        PkgSig bundle P pkg →
                                          SemanticNameCert
                                              (fun row : BHist =>
                                                hsame row structuralRead ∧
                                                  UnaryHistory row)
                                              (fun row : BHist =>
                                                hsame row S ∨ hsame row M ∨
                                                  hsame row Theta ∨ hsame row W0 ∨
                                                    hsame row W1 ∨ hsame row D ∨
                                                      hsame row R ∨ hsame row A ∨
                                                        hsame row E ∨ hsame row H ∨
                                                          hsame row structuralRead)
                                              (fun row : BHist =>
                                                UnaryHistory row ∧
                                                  PkgSig bundle P pkg)
                                              hsame ∧
                                            UnaryHistory structuralRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont UnaryHistory PkgSig hsame SemanticNameCert
  intro sourceUnary sealUnary thresholdUnary leftWindowUnary rightWindowUnary
    toleranceUnary _readbackUnary agreementUnary realUnary structuralUnary sourceSeal
    sourceThresholdSeal sealLeftWindow windowRightWindow rightTolerance toleranceReadback
    readbackAgreement agreementReal packageSig
  have sourceReadUnary : UnaryHistory sourceRead :=
    unary_cont_closed sourceUnary sealUnary sourceSeal
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed sourceReadUnary thresholdUnary sourceThresholdSeal
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed sealReadUnary leftWindowUnary sealLeftWindow
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowReadUnary rightWindowUnary windowRightWindow
  have readbackRouteUnary : UnaryHistory R :=
    unary_cont_closed toleranceReadUnary toleranceUnary rightTolerance
  have agreementReadUnary : UnaryHistory agreementRead :=
    unary_cont_closed readbackRouteUnary agreementUnary toleranceReadback
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed agreementReadUnary realUnary readbackAgreement
  have structuralReadUnary : UnaryHistory structuralRead :=
    unary_cont_closed realReadUnary structuralUnary agreementReal
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row structuralRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row M ∨ hsame row Theta ∨ hsame row W0 ∨
              hsame row W1 ∨ hsame row D ∨ hsame row R ∨ hsame row A ∨
                hsame row E ∨ hsame row H ∨ hsame row structuralRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro structuralRead
          ⟨hsame_refl structuralRead, structuralReadUnary⟩
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
      exact
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr
                        (Or.inr
                          (Or.inr source.left)))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, packageSig⟩
  }
  exact ⟨cert, structuralReadUnary⟩

end BEDC.Derived.CauchyTailThresholdNormalizerUp
