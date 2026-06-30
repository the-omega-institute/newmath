import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary

namespace BEDC.Derived

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary

inductive RegularCauchyApartnessReflectorUp : Type where
  | mk (S R D A L E H C N : BHist) : RegularCauchyApartnessReflectorUp
  deriving DecidableEq

def RegularCauchyApartnessReflectorCarrier
    (S R D A L E H C N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory RegularCauchyApartnessReflectorUp
  (∃ K : RegularCauchyApartnessReflectorUp,
      K = RegularCauchyApartnessReflectorUp.mk S R D A L E H C N) ∧
    UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory D ∧ UnaryHistory A ∧
      UnaryHistory L ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
        UnaryHistory N

theorem RegularCauchyApartnessReflectorNamecertObligations
    {S R D A L E H C N sourceRead dyadicRead locatedRead sealedRead : BHist} :
    RegularCauchyApartnessReflectorCarrier S R D A L E H C N →
      Cont S R sourceRead →
        Cont sourceRead D dyadicRead →
          Cont dyadicRead L locatedRead →
            Cont locatedRead E sealedRead →
              SemanticNameCert
                  (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
                      hsame row L ∨ hsame row E ∨ hsame row sealedRead)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont S R sourceRead ∧
                      Cont sourceRead D dyadicRead ∧ Cont dyadicRead L locatedRead ∧
                        Cont locatedRead E sealedRead)
                  hsame ∧
                UnaryHistory sourceRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory locatedRead ∧ UnaryHistory sealedRead := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute dyadicRoute locatedRoute sealedRoute
  obtain ⟨_packet, sUnary, rUnary, dUnary, _aUnary, lUnary, eUnary, _hUnary,
    _cUnary, _nUnary⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sUnary rUnary sourceRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed sourceUnary dUnary dyadicRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed dyadicUnary lUnary locatedRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed locatedUnary eUnary sealedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row R ∨ hsame row D ∨ hsame row A ∨
              hsame row L ∨ hsame row E ∨ hsame row sealedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S R sourceRead ∧
              Cont sourceRead D dyadicRead ∧ Cont dyadicRead L locatedRead ∧
                Cont locatedRead E sealedRead)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro sealedRead ⟨hsame_refl sealedRead, sealedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, sourceRoute, dyadicRoute, locatedRoute, sealedRoute⟩
  }
  exact ⟨cert, sourceUnary, dyadicUnary, locatedUnary, sealedUnary⟩

theorem RegularCauchyApartnessReflectorLocatedRealHandoff
    {S R D A L E H C N sourceRead dyadicRead locatedRead sealedRead : BHist} :
    RegularCauchyApartnessReflectorCarrier S R D A L E H C N →
      Cont S R sourceRead →
        Cont sourceRead D dyadicRead →
          Cont dyadicRead L locatedRead →
            Cont locatedRead E sealedRead →
              hsame A D →
                UnaryHistory sourceRead ∧ UnaryHistory dyadicRead ∧
                  UnaryHistory locatedRead ∧ UnaryHistory sealedRead ∧ hsame D A := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrier sourceRoute dyadicRoute locatedRoute sealedRoute sameApartness
  obtain ⟨_packet, sUnary, rUnary, dUnary, _aUnary, lUnary, eUnary, _hUnary,
    _cUnary, _nUnary⟩ := carrier
  have sourceUnary : UnaryHistory sourceRead :=
    unary_cont_closed sUnary rUnary sourceRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed sourceUnary dUnary dyadicRoute
  have locatedUnary : UnaryHistory locatedRead :=
    unary_cont_closed dyadicUnary lUnary locatedRoute
  have sealedUnary : UnaryHistory sealedRead :=
    unary_cont_closed locatedUnary eUnary sealedRoute
  exact
    ⟨sourceUnary, dyadicUnary, locatedUnary, sealedUnary,
      hsame_symm sameApartness⟩

end BEDC.Derived
