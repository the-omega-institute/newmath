import BEDC.Derived.CriticalLineWitnessUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_modulus_route_row
    {Z S M R Q H C P N modulusRead comparisonRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont M R modulusRead ->
        Cont modulusRead Q comparisonRead ->
          UnaryHistory M ∧ UnaryHistory R ∧ UnaryHistory Q ∧ UnaryHistory H ∧
            UnaryHistory C ∧ UnaryHistory N ∧ UnaryHistory modulusRead ∧
              UnaryHistory comparisonRead ∧ hsame H (append Z S) ∧
                Cont M R modulusRead ∧ Cont modulusRead Q comparisonRead ∧
                  Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro packet modulusRoute comparisonRoute
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
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryComparisonRead : UnaryHistory comparisonRead :=
    unary_cont_closed unaryModulusRead unaryQ comparisonRoute
  exact
    ⟨unaryM, unaryR, unaryQ, unaryH, unaryC, unaryN, unaryModulusRead,
      unaryComparisonRead, sameH, modulusRoute, comparisonRoute, routeC, routeN⟩

theorem CriticalLineWitnessCarrier_root_nonescape_ledger_row
    {Z S M R Q H C P N refusalRead ledgerRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont N Q refusalRead ->
        Cont refusalRead C ledgerRead ->
          SemanticNameCert
              (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
              (fun row : BHist => hsame row ledgerRead ∧ Cont N Q refusalRead)
              (fun row : BHist => hsame row ledgerRead ∧ Cont refusalRead C ledgerRead)
              hsame ∧
            UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory C ∧
              UnaryHistory N ∧ UnaryHistory refusalRead ∧ UnaryHistory ledgerRead ∧
                hsame H (append Z S) ∧ Cont M R Q ∧ Cont Q H C ∧ Cont C P N ∧
                  Cont N Q refusalRead ∧ Cont refusalRead C ledgerRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet refusalRoute ledgerRoute
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
  have unaryRefusalRead : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryLedgerRead : UnaryHistory ledgerRead :=
    unary_cont_closed unaryRefusalRead unaryC ledgerRoute
  have sourceAtLedger : hsame ledgerRead ledgerRead ∧ UnaryHistory ledgerRead :=
    ⟨hsame_refl ledgerRead, unaryLedgerRead⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row ledgerRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row ledgerRead ∧ Cont N Q refusalRead)
          (fun row : BHist => hsame row ledgerRead ∧ Cont refusalRead C ledgerRead)
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
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact ⟨source.left, refusalRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, ledgerRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryC, unaryN, unaryRefusalRead, unaryLedgerRead,
      sameH, routeQ, routeC, routeN, refusalRoute, ledgerRoute⟩

end BEDC.Derived.CriticalLineWitnessUp
