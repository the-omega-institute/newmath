import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyTailRequestUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

def CauchyTailRequestCarrier
    (W Q D R E H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  UnaryHistory W ∧ UnaryHistory Q ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N ∧ Cont H C P

theorem CauchyTailRequestCarrier_namecert_obligations
    {W Q D R E H C P N requestRead sealRead : BHist} :
    CauchyTailRequestCarrier W Q D R E H C P N →
      Cont W Q requestRead →
        Cont requestRead D R →
          Cont R E sealRead →
            SemanticNameCert
                (fun row : BHist =>
                  CauchyTailRequestCarrier W Q D R E H C P N ∧ hsame row N)
                (fun row : BHist =>
                  hsame row W ∨ hsame row Q ∨ hsame row D ∨ hsame row R ∨
                    hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                      hsame row N)
                (fun row : BHist => UnaryHistory row ∧ Cont R E sealRead)
                hsame ∧
              UnaryHistory requestRead ∧ UnaryHistory R ∧ UnaryHistory sealRead ∧
                Cont W Q requestRead ∧ Cont requestRead D R ∧ Cont R E sealRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier windowRequest requestReadback readbackSeal
  obtain ⟨wUnary, qUnary, dUnary, rUnary, eUnary, hUnary, cUnary, pUnary, nUnary,
    structuralReplay⟩ := carrier
  have carrierForSource :
      CauchyTailRequestCarrier W Q D R E H C P N :=
    ⟨wUnary, qUnary, dUnary, rUnary, eUnary, hUnary, cUnary, pUnary, nUnary,
      structuralReplay⟩
  have requestUnary : UnaryHistory requestRead :=
    unary_cont_closed wUnary qUnary windowRequest
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed rUnary eUnary readbackSeal
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro N ⟨carrierForSource, hsame_refl N⟩
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
          exact ⟨source.left, hsame_trans (hsame_symm sameRows) source.right⟩
      }
      pattern_sound := by
        intro _row source
        right
        right
        right
        right
        right
        right
        right
        right
        exact source.right
      ledger_sound := by
        intro _row source
        exact ⟨unary_transport nUnary (hsame_symm source.right), readbackSeal⟩
    }
  · exact
      ⟨requestUnary, rUnary, sealUnary, windowRequest, requestReadback, readbackSeal⟩

end BEDC.Derived.CauchyTailRequestUp
