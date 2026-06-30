import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert

namespace BEDC.Derived.RealZeroUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert

def RealZeroCarrier (q S Z0 D R H C P N : BHist) : Prop :=
  Cont q S Z0 ∧ Cont Z0 D R ∧ hsame H H ∧
    hsame C C ∧ hsame P P ∧ hsame N N ∧
    Nonempty (NameCert (fun row : BHist => hsame row R) hsame)

private def RealZeroCarrier_terminal_core (R : BHist) :
    NameCert (fun row : BHist => hsame row R) hsame where
  -- BEDC touchpoint anchor: BHist hsame NameCert
  carrier_inhabited := Exists.intro R (hsame_refl R)
  equiv_refl := by
    intro row _source
    exact hsame_refl row
  equiv_symm := by
    intro _row _other same
    exact hsame_symm same
  equiv_trans := by
    intro _row _other _third sameRO sameOT
    exact hsame_trans sameRO sameOT
  carrier_respects_equiv := by
    intro _row _other same source
    exact hsame_trans (hsame_symm same) source

theorem RealZeroCarrier_terminal_seal_handoff {q S Z0 D R H C P N : BHist} :
    RealZeroCarrier q S Z0 D R H C P N ->
      SemanticNameCert
          (fun row : BHist => hsame row R)
          (fun row : BHist =>
            hsame row q ∨ hsame row S ∨ hsame row Z0 ∨ hsame row D ∨
              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N)
          (fun row : BHist => hsame row R ∧ Cont q S Z0 ∧ Cont Z0 D R)
          hsame ∧
        Cont q S Z0 ∧ Cont Z0 D R := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro carrier
  cases carrier with
  | intro qToS rest =>
      cases rest with
      | intro zToD _rest =>
  constructor
  · exact {
      core := RealZeroCarrier_terminal_core R
      pattern_sound := by
        intro row source
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl source))))
      ledger_sound := by
        intro row source
        exact And.intro source (And.intro qToS zToD)
    }
  · exact And.intro qToS zToD

theorem RealZeroCarrier_stationary_source_obligation {q S Z0 D R H C P N : BHist} :
    RealZeroCarrier q S Z0 D R H C P N ->
      Nonempty (NameCert (fun row : BHist => hsame row Z0) hsame) ∧
        Cont q S Z0 ∧ hsame H H := by
  -- BEDC touchpoint anchor: BHist Cont hsame NameCert
  intro carrier
  cases carrier with
  | intro qToS rest =>
      cases rest with
      | intro _zToD rest =>
          cases rest with
          | intro sameH _rest =>
  constructor
  · exact
      Nonempty.intro {
        carrier_inhabited := Exists.intro Z0 (hsame_refl Z0)
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro _row _other same
          exact hsame_symm same
        equiv_trans := by
          intro _row _other _third sameRO sameOT
          exact hsame_trans sameRO sameOT
        carrier_respects_equiv := by
          intro _row _other same source
          exact hsame_trans (hsame_symm same) source
      }
  · exact And.intro qToS sameH

end BEDC.Derived.RealZeroUp
