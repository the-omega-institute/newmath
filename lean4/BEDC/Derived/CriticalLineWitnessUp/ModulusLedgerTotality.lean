import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_modulus_ledger_totality
    {Z S M R Q H C P N modulusRead realRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N →
      Cont M R modulusRead →
        Cont modulusRead Q realRead →
          Cont realRead H ledgerRead →
            SemanticNameCert
                (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨
                    hsame row ledgerRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont M R modulusRead ∧
                    Cont modulusRead Q realRead ∧ Cont realRead H ledgerRead ∧
                      Cont M R Q ∧ Cont Q H C ∧ Cont C P N)
                hsame ∧
              UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                UnaryHistory modulusRead ∧ UnaryHistory realRead ∧ UnaryHistory ledgerRead ∧
                  hsame H (append Z S) ∧ Cont M R Q ∧ Cont M R modulusRead ∧
                    Cont modulusRead Q realRead ∧ Cont realRead H ledgerRead ∧
                      Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet modulusRoute realRoute ledgerRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have _unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have realUnary : UnaryHistory realRead :=
    unary_cont_closed modulusUnary unaryQ realRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed realUnary unaryH ledgerRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row R ∨ hsame row Q ∨ hsame row H ∨ hsame row ledgerRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M R modulusRead ∧ Cont modulusRead Q realRead ∧
              Cont realRead H ledgerRead ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro ledgerRead ⟨hsame_refl ledgerRead, ledgerUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, modulusRoute, realRoute, ledgerRoute, routeQ, routeC, routeN⟩
  }
  exact
    ⟨cert, unaryM, unaryR, unaryQ, unaryH, modulusUnary, realUnary, ledgerUnary, sameH,
      routeQ, modulusRoute, realRoute, ledgerRoute, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
