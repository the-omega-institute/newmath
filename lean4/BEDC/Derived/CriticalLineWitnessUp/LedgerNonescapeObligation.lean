import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_ledger_nonescape_obligation
    {Z S M R Q H C P N ledgerRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M Q ledgerRead ->
        Cont ledgerRead N publicRead ->
          SemanticNameCert
              (fun row : BHist =>
                (hsame row ledgerRead ∨ hsame row publicRead ∨ hsame row Q ∨
                  hsame row N) ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row M ∨ hsame row Q ∨ hsame row ledgerRead ∨ hsame row N ∨
                  hsame row publicRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont M Q ledgerRead ∧ Cont ledgerRead N publicRead ∧
                  Cont M R Q ∧ Cont Q H C ∧ Cont C P N)
              hsame ∧
            UnaryHistory ledgerRead ∧ UnaryHistory publicRead ∧ hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet ledgerRoute publicRoute
  have closure :
      UnaryHistory Q ∧ UnaryHistory C ∧ UnaryHistory N ∧ hsame H (append Z S) :=
    CriticalLineWitnessCarrier_modulus_route_closure packet
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    closure.left
  have unaryN : UnaryHistory N :=
    closure.right.right.left
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed unaryM unaryQ ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary unaryN publicRoute
  have sourceAtLedger :
      (hsame ledgerRead ledgerRead ∨ hsame ledgerRead publicRead ∨ hsame ledgerRead Q ∨
        hsame ledgerRead N) ∧ UnaryHistory ledgerRead :=
    ⟨Or.inl (hsame_refl ledgerRead), ledgerUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            (hsame row ledgerRead ∨ hsame row publicRead ∨ hsame row Q ∨
              hsame row N) ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row Q ∨ hsame row ledgerRead ∨ hsame row N ∨
              hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q ledgerRead ∧ Cont ledgerRead N publicRead ∧
              Cont M R Q ∧ Cont Q H C ∧ Cont C P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead sourceAtLedger
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
          ⟨match source.left with
            | Or.inl sameLedger =>
                Or.inl (hsame_trans (hsame_symm sameRows) sameLedger)
            | Or.inr (Or.inl samePublic) =>
                Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) samePublic))
            | Or.inr (Or.inr (Or.inl sameQ)) =>
                Or.inr (Or.inr (Or.inl (hsame_trans (hsame_symm sameRows) sameQ)))
            | Or.inr (Or.inr (Or.inr sameN)) =>
                Or.inr (Or.inr (Or.inr (hsame_trans (hsame_symm sameRows) sameN))),
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      cases source.left with
      | inl sameLedger =>
          exact Or.inr (Or.inr (Or.inl sameLedger))
      | inr rest =>
          cases rest with
          | inl samePublic =>
              exact Or.inr (Or.inr (Or.inr (Or.inr samePublic)))
          | inr rest =>
              cases rest with
              | inl sameQ =>
                  exact Or.inr (Or.inl sameQ)
              | inr sameN =>
                  exact Or.inr (Or.inr (Or.inr (Or.inl sameN)))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, ledgerRoute, publicRoute, routeQ, routeC, routeN⟩
  }
  exact ⟨cert, ledgerUnary, publicUnary, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
