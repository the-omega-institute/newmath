import BEDC.Derived.FiniteLowerBoundFoldUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.FiniteLowerBoundFoldUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem FiniteLowerBoundFoldCarrier_uniform_modulus_handoff [AskSetup] [PackageSetup]
    {K P R A B L H C Q N foldRead handoffRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory A →
      UnaryHistory B →
        UnaryHistory L →
          Cont A B foldRead →
            Cont foldRead L handoffRead →
              PkgSig bundle Q pkg →
                PkgSig bundle N pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row K ∨ hsame row P ∨ hsame row R ∨ hsame row A ∨
                          hsame row B ∨ hsame row L ∨ hsame row H ∨ hsame row C ∨
                            hsame row Q ∨ hsame row N ∨ hsame row foldRead ∨
                              hsame row handoffRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont A B foldRead ∧ Cont foldRead L handoffRead ∧
                          PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
                      hsame ∧ UnaryHistory foldRead ∧ UnaryHistory handoffRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro unaryA unaryB unaryL foldRoute handoffRoute sourcePkg namePkg
  have foldUnary : UnaryHistory foldRead :=
    unary_cont_closed unaryA unaryB foldRoute
  have handoffUnary : UnaryHistory handoffRead :=
    unary_cont_closed foldUnary unaryL handoffRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row handoffRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row K ∨ hsame row P ∨ hsame row R ∨ hsame row A ∨ hsame row B ∨
              hsame row L ∨ hsame row H ∨ hsame row C ∨ hsame row Q ∨ hsame row N ∨
                hsame row foldRead ∨ hsame row handoffRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont A B foldRead ∧ Cont foldRead L handoffRead ∧
              PkgSig bundle Q pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro handoffRead ⟨hsame_refl handoffRead, handoffUnary⟩
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
                          (Or.inr
                            (Or.inr source.left))))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, foldRoute, handoffRoute, sourcePkg, namePkg⟩
  }
  exact ⟨cert, foldUnary, handoffUnary⟩

end BEDC.Derived.FiniteLowerBoundFoldUp
