import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_nonescape_package
    {Z S M R Q H C P N zeroStripRead modulusRead ledgerRead refusalRead : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R modulusRead ->
          Cont modulusRead H ledgerRead ->
            Cont N Q refusalRead ->
              SemanticNameCert
                  (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
                  (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
                  (fun row : BHist =>
                    hsame row refusalRead ∧ Cont modulusRead H ledgerRead)
                  hsame ∧
                UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory M ∧ UnaryHistory R ∧
                  UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory N ∧
                    UnaryHistory zeroStripRead ∧ UnaryHistory modulusRead ∧
                      UnaryHistory ledgerRead ∧ UnaryHistory refusalRead ∧
                        hsame H (append Z S) ∧ Cont Z S zeroStripRead ∧
                          Cont M R modulusRead ∧ Cont modulusRead H ledgerRead ∧
                            Cont N Q refusalRead ∧ Cont M R Q ∧ Cont Q H C ∧
                              Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute modulusRoute ledgerRoute refusalRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryAppend : UnaryHistory (append Z S) :=
    unary_cont_closed unaryZ unaryS (cont_intro rfl)
  have unaryH : UnaryHistory H :=
    unary_transport unaryAppend (hsame_symm sameH)
  have unaryC : UnaryHistory C :=
    unary_cont_closed unaryQ unaryH routeC
  have unaryN : UnaryHistory N :=
    unary_cont_closed unaryC unaryP routeN
  have zeroStripUnary : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have modulusUnary : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have ledgerUnary : UnaryHistory ledgerRead :=
    unary_cont_closed modulusUnary unaryH ledgerRoute
  have refusalUnary : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have sourceAtRefusal : hsame refusalRead refusalRead ∧ UnaryHistory refusalRead :=
    ⟨hsame_refl refusalRead, refusalUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row refusalRead ∧ UnaryHistory row)
          (fun row : BHist => hsame row refusalRead ∧ Cont N Q refusalRead)
          (fun row : BHist => hsame row refusalRead ∧ Cont modulusRead H ledgerRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro refusalRead sourceAtRefusal
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
    ⟨cert, unaryZ, unaryS, unaryM, unaryR, unaryQ, unaryH, unaryN, zeroStripUnary,
      modulusUnary, ledgerUnary, refusalUnary, sameH, zeroStripRoute, modulusRoute,
      ledgerRoute, refusalRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
