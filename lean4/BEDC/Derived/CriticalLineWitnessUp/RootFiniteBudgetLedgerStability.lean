import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessRootFiniteBudgetLedgerStability
    {Z S M R Q H C P N Qp Cp : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R Qp ->
        Cont Qp H Cp ->
          hsame Cp C ->
            SemanticNameCert
                (fun row : BHist =>
                  (hsame row Qp ∨ hsame row Cp ∨ hsame row Q ∨ hsame row C) ∧
                    UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row R ∨ hsame row Qp ∨ hsame row Cp ∨
                    hsame row Q ∨ hsame row C ∨ hsame row H)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M R Qp ∧ Cont Qp H Cp ∧ hsame Qp Q ∧
                    hsame Cp C ∧ Cont M R Q ∧ Cont Q H C)
                hsame ∧
              hsame Qp Q ∧ UnaryHistory Qp ∧ UnaryHistory Cp ∧
                hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet routeQp routeCp sameCp
  obtain ⟨sameQp, unaryQp, unaryCp, sameH⟩ :=
    CriticalLineWitnessCarrier_modulus_depth_route_determinacy packet routeQp routeCp sameCp
  obtain ⟨_unaryZ, _unaryS, _unaryM, _unaryR, _unaryP, _sameH, routeQ, routeC, _routeN⟩ :=
    packet
  have sourceAtQp :
      (hsame Qp Qp ∨ hsame Qp Cp ∨ hsame Qp Q ∨ hsame Qp C) ∧
        UnaryHistory Qp :=
    ⟨Or.inl (hsame_refl Qp), unaryQp⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row Qp ∨ hsame row Cp ∨ hsame row Q ∨ hsame row C) ∧
              UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Qp ∨ hsame row Cp ∨
              hsame row Q ∨ hsame row C ∨ hsame row H)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R Qp ∧ Cont Qp H Cp ∧ hsame Qp Q ∧
              hsame Cp C ∧ Cont M R Q ∧ Cont Q H C)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro Qp sourceAtQp
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
        cases sameRows
        exact source
    }
    pattern_sound := by
      intro row source
      cases source.left with
      | inl sameRowQp =>
          exact Or.inr (Or.inr (Or.inl sameRowQp))
      | inr rest =>
          cases rest with
          | inl sameRowCp =>
              exact Or.inr (Or.inr (Or.inr (Or.inl sameRowCp)))
          | inr restTail =>
              cases restTail with
              | inl sameRowQ =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRowQ))))
              | inr sameRowC =>
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl sameRowC)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeQp, routeCp, sameQp, sameCp, routeQ, routeC⟩
  }
  exact ⟨cert, sameQp, unaryQp, unaryCp, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
