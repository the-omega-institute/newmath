import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_root_zero_strip_readback
    {Z S M R Q H C P N zeroRead modulusRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroRead ->
        Cont zeroRead Q modulusRead ->
          Cont modulusRead H readback ->
            SemanticNameCert
                (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                (fun row : BHist => hsame row readback ∧ Cont Z S zeroRead)
                (fun row : BHist => hsame row readback ∧ Cont modulusRead H readback)
                hsame ∧
              UnaryHistory Z ∧ UnaryHistory S ∧ UnaryHistory Q ∧ UnaryHistory H ∧
                UnaryHistory zeroRead ∧ UnaryHistory modulusRead ∧ UnaryHistory readback ∧
                  hsame H (append Z S) ∧ Cont Z S zeroRead ∧
                    Cont zeroRead Q modulusRead ∧ Cont modulusRead H readback ∧
                      Cont M R Q ∧ Cont Q H C ∧ Cont C P N := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroRoute modulusRoute readbackRoute
  obtain ⟨unaryZ, unaryS, unaryM, unaryR, _unaryP, sameH, routeQ, routeC, routeN⟩ :=
    packet
  have unaryQ : UnaryHistory Q :=
    unary_cont_closed unaryM unaryR routeQ
  have unaryH : UnaryHistory H :=
    unary_transport (unary_cont_closed unaryZ unaryS (cont_intro rfl)) (hsame_symm sameH)
  have unaryZeroRead : UnaryHistory zeroRead :=
    unary_cont_closed unaryZ unaryS zeroRoute
  have unaryModulusRead : UnaryHistory modulusRead :=
    unary_cont_closed unaryZeroRead unaryQ modulusRoute
  have unaryReadback : UnaryHistory readback :=
    unary_cont_closed unaryModulusRead unaryH readbackRoute
  have sourceAtReadback : hsame readback readback ∧ UnaryHistory readback :=
    ⟨hsame_refl readback, unaryReadback⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist => hsame row readback ∧ Cont Z S zeroRead)
          (fun row : BHist => hsame row readback ∧ Cont modulusRead H readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback sourceAtReadback
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
      exact ⟨source.left, zeroRoute⟩
    ledger_sound := by
      intro _row source
      exact ⟨source.left, readbackRoute⟩
  }
  exact
    ⟨cert, unaryZ, unaryS, unaryQ, unaryH, unaryZeroRead, unaryModulusRead,
      unaryReadback, sameH, zeroRoute, modulusRoute, readbackRoute, routeQ, routeC, routeN⟩

end BEDC.Derived.CriticalLineWitnessUp
