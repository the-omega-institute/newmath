import BEDC.Derived.CriticalLineWitnessUp

namespace BEDC.Derived.CriticalLineWitnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem CriticalLineWitnessCarrier_rh_refusal_readback_totality
    {Z S M R Q H C P N zeroStripRead modulusRead refusalRead readback : BHist} :
    CriticalLineWitnessCarrier Z S M R Q H C P N ->
      Cont Z S zeroStripRead ->
        Cont M R modulusRead ->
          Cont N Q refusalRead ->
            Cont refusalRead C readback ->
              SemanticNameCert
                  (fun row : BHist => hsame row readback ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row zeroStripRead ∨ hsame row modulusRead ∨
                      hsame row refusalRead ∨ hsame row readback ∨ hsame row N ∨
                        hsame row Q)
                  (fun row : BHist =>
                    hsame row readback ∧ Cont Z S zeroStripRead ∧
                      Cont M R modulusRead ∧ Cont N Q refusalRead ∧
                        Cont refusalRead C readback)
                  hsame ∧
                UnaryHistory zeroStripRead ∧ UnaryHistory modulusRead ∧
                  UnaryHistory refusalRead ∧ UnaryHistory readback := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro packet zeroStripRoute modulusRoute refusalRoute readbackRoute
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
  have unaryZeroStrip : UnaryHistory zeroStripRead :=
    unary_cont_closed unaryZ unaryS zeroStripRoute
  have unaryModulus : UnaryHistory modulusRead :=
    unary_cont_closed unaryM unaryR modulusRoute
  have unaryRefusal : UnaryHistory refusalRead :=
    unary_cont_closed unaryN unaryQ refusalRoute
  have unaryReadback : UnaryHistory readback :=
    unary_cont_closed unaryRefusal unaryC readbackRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row readback ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row zeroStripRead ∨ hsame row modulusRead ∨ hsame row refusalRead ∨
              hsame row readback ∨ hsame row N ∨ hsame row Q)
          (fun row : BHist =>
            hsame row readback ∧ Cont Z S zeroStripRead ∧ Cont M R modulusRead ∧
              Cont N Q refusalRead ∧ Cont refusalRead C readback)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro readback ⟨hsame_refl readback, unaryReadback⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inl source.left)))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, zeroStripRoute, modulusRoute, refusalRoute, readbackRoute⟩
  }
  exact ⟨cert, unaryZeroStrip, unaryModulus, unaryRefusal, unaryReadback⟩

end BEDC.Derived.CriticalLineWitnessUp
