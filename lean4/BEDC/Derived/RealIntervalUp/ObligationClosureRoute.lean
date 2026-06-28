import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalCarrier_obligation_closure_route [AskSetup] [PackageSetup]
    {L U E D W R S H C P N : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory N → Cont L U E → Cont D W R → Cont E R S →
        Cont S H C → Cont C N N → PkgSig bundle P pkg → PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist => hsame row S ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
                  hsame row W ∨ hsame row R ∨ hsame row S ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont L U E ∧ Cont D W R ∧ Cont E R S ∧
                  Cont S H C ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory C := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary eUnary dUnary wUnary hUnary _nUnary _endpointRoute windowRoute
    sealRoute consumerRoute _nameRoute provenancePkg namePkg
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary windowRoute
  have sealUnary : UnaryHistory S :=
    unary_cont_closed eUnary readbackUnary sealRoute
  have consumerUnary : UnaryHistory C :=
    unary_cont_closed sealUnary hUnary consumerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row S ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont L U E ∧ Cont D W R ∧ Cont E R S ∧ Cont S H C ∧
              PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro S ⟨hsame_refl S, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, _endpointRoute, windowRoute, sealRoute, consumerRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, readbackUnary, sealUnary, consumerUnary⟩

end BEDC.Derived.RealIntervalUp
