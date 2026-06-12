import BEDC.Derived.BanachSpaceUp.NameCertFrontier

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

set_option linter.unusedVariables false

theorem BanachSpaceVectorOperationTransportObligation [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L vectorRead transportedRead localRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory V ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧
      PkgSig bundle P pkg ∧ PkgSig bundle L pkg) →
      Cont V H vectorRead →
        Cont vectorRead C transportedRead →
          Cont transportedRead L localRead →
            PkgSig bundle localRead pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row V ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row L ∨ hsame row localRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont V H vectorRead ∧
                      Cont vectorRead C transportedRead ∧
                        Cont transportedRead L localRead ∧ PkgSig bundle localRead pkg)
                  hsame ∧
                UnaryHistory vectorRead ∧ UnaryHistory transportedRead ∧
                  UnaryHistory localRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert UnaryHistory
  intro surface vectorRoute transportRoute localRoute localPkg
  have vUnary : UnaryHistory V := surface.left
  have hUnary : UnaryHistory H := surface.right.left
  have cUnary : UnaryHistory C := surface.right.right.left
  have lUnary : UnaryHistory L := surface.right.right.right.right.left
  have vectorUnary : UnaryHistory vectorRead :=
    unary_cont_closed vUnary hUnary vectorRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed vectorUnary cUnary transportRoute
  have localUnary : UnaryHistory localRead :=
    unary_cont_closed transportedUnary lUnary localRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row localRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row L ∨
              hsame row localRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont V H vectorRead ∧ Cont vectorRead C transportedRead ∧
              Cont transportedRead L localRead ∧ PkgSig bundle localRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro localRead ⟨hsame_refl localRead, localUnary⟩
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
                (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, vectorRoute, transportRoute, localRoute, localPkg⟩
  }
  exact ⟨cert, vectorUnary, transportedUnary, localUnary⟩

end BEDC.Derived.BanachSpaceUp
