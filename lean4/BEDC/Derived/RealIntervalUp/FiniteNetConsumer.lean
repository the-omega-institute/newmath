import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalFiniteNetConsumer [AskSetup] [PackageSetup]
    {L U E D W R S H C P N netRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory N → Cont D W R → Cont E R S → Cont S H C →
        Cont C N netRead → PkgSig bundle P pkg → PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist => hsame row netRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
                  hsame row W ∨ hsame row R ∨ hsame row S ∨ hsame row H ∨
                    hsame row C ∨ hsame row N ∨ hsame row netRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D W R ∧ Cont E R S ∧ Cont S H C ∧
                  Cont C N netRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory netRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary eUnary dUnary wUnary hUnary nUnary windowRoute sealRoute
    consumerRoute netRoute provenancePkg namePkg
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary windowRoute
  have sealUnary : UnaryHistory S :=
    unary_cont_closed eUnary readbackUnary sealRoute
  have consumerUnary : UnaryHistory C :=
    unary_cont_closed sealUnary hUnary consumerRoute
  have netUnary : UnaryHistory netRead :=
    unary_cont_closed consumerUnary nUnary netRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row netRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row N ∨
                hsame row netRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W R ∧ Cont E R S ∧ Cont S H C ∧
              Cont C N netRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro netRead ⟨hsame_refl netRead, netUnary⟩
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
      exact
        ⟨source.right, windowRoute, sealRoute, consumerRoute, netRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, readbackUnary, sealUnary, consumerUnary, netUnary⟩

end BEDC.Derived.RealIntervalUp
