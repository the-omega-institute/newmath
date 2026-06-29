import BEDC.Derived.SeparableCompletionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.SeparableCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SeparableCompletionCarrier [AskSetup] [PackageSetup]
    (metric dense completion windows tolerance readback sealRow transport provenance
      localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory metric ∧ UnaryHistory dense ∧ UnaryHistory completion ∧
    UnaryHistory windows ∧ UnaryHistory tolerance ∧ UnaryHistory readback ∧
      UnaryHistory sealRow ∧ UnaryHistory transport ∧ UnaryHistory provenance ∧
        UnaryHistory localName ∧ PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

theorem SeparableCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {metric dense completion windows tolerance readback sealRow transport provenance localName
      windowRead toleranceRead completionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory metric →
      UnaryHistory dense →
        UnaryHistory completion →
          UnaryHistory windows →
            UnaryHistory tolerance →
              UnaryHistory readback →
                UnaryHistory sealRow →
                  UnaryHistory transport →
                    PkgSig bundle provenance pkg →
                      PkgSig bundle localName pkg →
                        Cont dense windows windowRead →
                          Cont windowRead tolerance toleranceRead →
                            Cont toleranceRead completion completionRead →
                              PkgSig bundle completionRead pkg →
                                SemanticNameCert
                                    (fun row : BHist =>
                                      hsame row completionRead ∧ UnaryHistory row)
                                    (fun row : BHist =>
                                      hsame row metric ∨ hsame row dense ∨
                                        hsame row windows ∨ hsame row tolerance ∨
                                          hsame row readback ∨ hsame row sealRow ∨
                                            hsame row completionRead)
                                    (fun row : BHist =>
                                      UnaryHistory row ∧ Cont dense windows windowRead ∧
                                        Cont windowRead tolerance toleranceRead ∧
                                          Cont toleranceRead completion completionRead ∧
                                            PkgSig bundle provenance pkg ∧
                                              PkgSig bundle localName pkg)
                                    hsame ∧
                                    UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                                    UnaryHistory completionRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro _metricUnary denseUnary completionUnary windowsUnary toleranceUnary _readbackUnary
    _sealUnary _transportUnary provenancePkg localNamePkg denseWindowsWindow
    windowToleranceTolerance toleranceCompletionCompletion _completionPkg
  have windowUnary : UnaryHistory windowRead :=
    unary_cont_closed denseUnary windowsUnary denseWindowsWindow
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary toleranceUnary windowToleranceTolerance
  have completionReadUnary : UnaryHistory completionRead :=
    unary_cont_closed toleranceReadUnary completionUnary toleranceCompletionCompletion
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row completionRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row metric ∨ hsame row dense ∨ hsame row windows ∨
              hsame row tolerance ∨ hsame row readback ∨ hsame row sealRow ∨
                hsame row completionRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont dense windows windowRead ∧
              Cont windowRead tolerance toleranceRead ∧
                Cont toleranceRead completion completionRead ∧
                  PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro completionRead ⟨hsame_refl completionRead, completionReadUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, denseWindowsWindow, windowToleranceTolerance,
          toleranceCompletionCompletion, provenancePkg, localNamePkg⟩
  }
  exact ⟨cert, windowUnary, toleranceReadUnary, completionReadUnary⟩

end BEDC.Derived.SeparableCompletionUp
