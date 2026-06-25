import BEDC.Derived.CauchyContinuousExtensionUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyContinuousExtensionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyContinuousExtensionNameCertObligations [AskSetup] [PackageSetup]
    {S W D F U L H C P N extensionRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory S →
      UnaryHistory W →
        UnaryHistory D →
          UnaryHistory F →
            UnaryHistory U →
              UnaryHistory L →
                Cont S W D →
                  Cont D F U →
                    Cont U L extensionRead →
                      PkgSig bundle P pkg →
                        PkgSig bundle N pkg →
                          SemanticNameCert
                            (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row F ∨
                                hsame row U ∨ hsame row extensionRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ Cont S W D ∧ Cont D F U ∧
                                Cont U L extensionRead ∧ PkgSig bundle P pkg ∧
                                  PkgSig bundle N pkg)
                            hsame ∧
                            UnaryHistory extensionRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro sUnary wUnary dUnary fUnary uUnary lUnary sourceRoute extensionRoute
    uniquenessRoute packageP packageN
  have extensionUnary : UnaryHistory extensionRead :=
    unary_cont_closed uUnary lUnary uniquenessRoute
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row extensionRead ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row F ∨ hsame row U ∨
            hsame row extensionRead)
        (fun row : BHist =>
          UnaryHistory row ∧ Cont S W D ∧ Cont D F U ∧ Cont U L extensionRead ∧
            PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
        hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro extensionRead ⟨hsame_refl extensionRead, extensionUnary⟩
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
        ⟨source.right, sourceRoute, extensionRoute, uniquenessRoute, packageP,
          packageN⟩
  }
  exact ⟨cert, extensionUnary⟩

end BEDC.Derived.CauchyContinuousExtensionUp
