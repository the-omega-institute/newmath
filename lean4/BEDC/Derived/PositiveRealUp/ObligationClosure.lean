import BEDC.Derived.PositiveRealUp.TasteGate

namespace BEDC.Derived.PositiveRealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

theorem PositiveRealCarrier_obligation_closure
    {R A D W Q H C P N apartnessRead windowRead closureRead : BHist} :
    PositiveRealCarrier R A D W Q H C P N →
      Cont A D apartnessRead →
        Cont W Q windowRead →
          Cont apartnessRead windowRead closureRead →
            UnaryHistory apartnessRead ∧ UnaryHistory windowRead ∧
              UnaryHistory closureRead ∧
                SemanticNameCert
                  (fun row : BHist => hsame row closureRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row R ∨ hsame row A ∨ hsame row D ∨ hsame row W ∨
                      hsame row Q ∨ hsame row closureRead)
                  (fun row : BHist =>
                    hsame row closureRead ∧ Cont A D apartnessRead ∧
                      Cont W Q windowRead)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier apartnessRoute windowRoute closureRoute
  obtain ⟨_realUnary, apartnessUnary, radiusUnary, windowUnary, readbackUnary,
    _handoffUnary, _replayUnary, _pkgUnary, _nameUnary⟩ := carrier
  have apartnessReadUnary : UnaryHistory apartnessRead :=
    unary_cont_closed apartnessUnary radiusUnary apartnessRoute
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary readbackUnary windowRoute
  have closureReadUnary : UnaryHistory closureRead :=
    unary_cont_closed apartnessReadUnary windowReadUnary closureRoute
  refine ⟨apartnessReadUnary, windowReadUnary, closureReadUnary, ?cert⟩
  refine
    { core :=
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · exact ⟨closureRead, hsame_refl closureRead, closureReadUnary⟩
  · intro row _source
    exact hsame_refl row
  · intro _row _other same
    exact hsame_symm same
  · intro _row _middle _other sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _row _other same source
    exact
      ⟨hsame_trans (hsame_symm same) source.left,
        unary_transport source.right same⟩
  · intro _row source
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
  · intro _row source
    exact ⟨source.left, apartnessRoute, windowRoute⟩

end BEDC.Derived.PositiveRealUp
