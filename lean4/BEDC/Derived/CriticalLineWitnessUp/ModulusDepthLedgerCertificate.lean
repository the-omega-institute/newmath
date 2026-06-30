import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_depth_ledger_certificate
    {Z S M R Q H C P N stripRead depthRead comparisonRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S stripRead ->
        Cont M R depthRead ->
          Cont depthRead Q comparisonRead ->
            Cont comparisonRead H ledgerRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨
                      hsame row Q ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                        hsame row N ∨ hsame row ledgerRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont Z S stripRead ∧ Cont M R depthRead ∧
                      Cont depthRead Q comparisonRead ∧
                        Cont comparisonRead H ledgerRead ∧ Cont Q H C ∧ Cont C P N)
                  hsame ∧
                UnaryHistory stripRead ∧ UnaryHistory depthRead ∧
                  UnaryHistory comparisonRead ∧ UnaryHistory ledgerRead ∧
                    hsame H (append Z S) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory append
  intro packet stripRoute depthRoute comparisonRoute ledgerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, _routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR _routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryStrip : UnaryHistory stripRead :=
    unary_cont_closed unaryZ unaryS stripRoute
  have unaryDepth : UnaryHistory depthRead :=
    unary_cont_closed unaryM unaryR depthRoute
  have unaryComparison : UnaryHistory comparisonRead :=
    unary_cont_closed unaryDepth unaryQ comparisonRoute
  have unaryLedger : UnaryHistory ledgerRead :=
    unary_cont_closed unaryComparison unaryH ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Z ∨ hsame row S ∨ hsame row M ∨ hsame row R ∨ hsame row Q ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Z S stripRead ∧ Cont M R depthRead ∧
              Cont depthRead Q comparisonRead ∧ Cont comparisonRead H ledgerRead ∧
                Cont Q H C ∧ Cont C P N)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro ledgerRead ⟨hsame_refl ledgerRead, unaryLedger⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, stripRoute, depthRoute, comparisonRoute, ledgerRoute, routeC,
          routeN⟩
  }
  exact ⟨cert, unaryStrip, unaryDepth, unaryComparison, unaryLedger, sameH⟩

end BEDC.Derived.CriticalLineWitnessUp
