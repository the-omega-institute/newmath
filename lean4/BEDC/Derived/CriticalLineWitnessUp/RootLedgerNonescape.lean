import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_ledger_nonescape
    {Z S M R Q H C P N refusalRead ledgerRead publicRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead P ledgerRead ->
          Cont ledgerRead C publicRead ->
            SemanticNameCert
                (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row refusalRead ∨ hsame row ledgerRead ∨ hsame row publicRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont N Q refusalRead ∧
                    Cont refusalRead P ledgerRead ∧ Cont ledgerRead C publicRead ∧
                      hsame row publicRead)
                hsame ∧
              UnaryHistory refusalRead ∧ UnaryHistory ledgerRead ∧
                UnaryHistory publicRead ∧ Cont N Q refusalRead ∧
                  Cont refusalRead P ledgerRead ∧ Cont ledgerRead C publicRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute ledgerRoute publicRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed refusalUnary unaryP ledgerRoute
  have publicUnary : UnaryHistory publicRead :=
    unary_cont_closed ledgerUnary unaryC publicRoute
  have sourceAtPublic : hsame publicRead publicRead ∧ UnaryHistory publicRead :=
    ⟨hsame_refl publicRead, publicUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row refusalRead ∨ hsame row ledgerRead ∨ hsame row publicRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont N Q refusalRead ∧ Cont refusalRead P ledgerRead ∧
              Cont ledgerRead C publicRead ∧ hsame row publicRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicRead sourceAtPublic
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
      exact Or.inr (Or.inr source.left)
    ledger_sound := by
      intro _row source
      exact ⟨source.right, refusalRoute, ledgerRoute, publicRoute, source.left⟩
  }
  exact
    ⟨cert, refusalUnary, ledgerUnary, publicUnary, refusalRoute, ledgerRoute,
      publicRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
