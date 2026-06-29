import BEDC.Derived.RealIntervalUp.TasteGate

namespace BEDC.Derived.RealIntervalUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RealIntervalBridgedNameCertRoute [AskSetup] [PackageSetup]
    {L U E D W R S H C P N bridgeRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L → UnaryHistory U → UnaryHistory E → UnaryHistory D → UnaryHistory W →
      UnaryHistory H → UnaryHistory P → Cont D W R → Cont E R S → Cont S H C →
        Cont C P bridgeRead → PkgSig bundle P pkg → PkgSig bundle N pkg →
          SemanticNameCert
              (fun row : BHist =>
                (hsame row bridgeRead ∨ hsame row S ∨ hsame row P) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨
                  hsame row W ∨ hsame row R ∨ hsame row S ∨ hsame row H ∨
                    hsame row C ∨ hsame row P ∨ hsame row N ∨ hsame row bridgeRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont D W R ∧ Cont E R S ∧ Cont S H C ∧
                  Cont C P bridgeRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
              hsame ∧
            UnaryHistory R ∧ UnaryHistory S ∧ UnaryHistory C ∧ UnaryHistory bridgeRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert UnaryHistory
  intro _lUnary _uUnary eUnary dUnary wUnary hUnary pUnary windowRoute sealRoute
    consumerRoute bridgeRoute provenancePkg namePkg
  have readbackUnary : UnaryHistory R :=
    unary_cont_closed dUnary wUnary windowRoute
  have sealUnary : UnaryHistory S :=
    unary_cont_closed eUnary readbackUnary sealRoute
  have consumerUnary : UnaryHistory C :=
    unary_cont_closed sealUnary hUnary consumerRoute
  have bridgeUnary : UnaryHistory bridgeRead :=
    unary_cont_closed consumerUnary pUnary bridgeRoute
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row bridgeRead ∨ hsame row S ∨ hsame row P) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row L ∨ hsame row U ∨ hsame row E ∨ hsame row D ∨ hsame row W ∨
              hsame row R ∨ hsame row S ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                hsame row N ∨ hsame row bridgeRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W R ∧ Cont E R S ∧ Cont S H C ∧
              Cont C P bridgeRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro bridgeRead ⟨Or.inl (hsame_refl bridgeRead), bridgeUnary⟩
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
        intro row other sameRows sourceRow
        have lift : forall {target : BHist}, hsame row target → hsame other target := by
          intro _target sameTarget
          exact hsame_trans (hsame_symm sameRows) sameTarget
        constructor
        · cases sourceRow.left with
          | inl sameBridge =>
              exact Or.inl (lift sameBridge)
          | inr rest =>
              cases rest with
              | inl sameSeal =>
                  exact Or.inr (Or.inl (lift sameSeal))
              | inr sameProvenance =>
                  exact Or.inr (Or.inr (lift sameProvenance))
        · exact unary_transport sourceRow.right sameRows
    }
    pattern_sound := by
      intro _row sourceRow
      cases sourceRow.left with
      | inl sameBridge =>
          repeat (first | exact sameBridge | apply Or.inr)
      | inr rest =>
          cases rest with
          | inl sameSeal =>
              repeat (first | exact Or.inl sameSeal | apply Or.inr)
          | inr sameProvenance =>
              repeat (first | exact Or.inl sameProvenance | apply Or.inr)
    ledger_sound := by
      intro _row sourceRow
      exact
        ⟨sourceRow.right, windowRoute, sealRoute, consumerRoute, bridgeRoute, provenancePkg,
          namePkg⟩
  }
  exact ⟨cert, readbackUnary, sealUnary, consumerUnary, bridgeUnary⟩

end BEDC.Derived.RealIntervalUp
