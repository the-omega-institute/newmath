import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DiagonalLimitObserverUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DiagonalLimitObserverUp : Type where
  | mk : (D W Q T S R H C P N : BHist) → DiagonalLimitObserverUp
  deriving DecidableEq

def diagonalLimitObserverEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: diagonalLimitObserverEncodeBHist h
  | BHist.e1 h => BMark.b1 :: diagonalLimitObserverEncodeBHist h

def diagonalLimitObserverDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (diagonalLimitObserverDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (diagonalLimitObserverDecodeBHist tail)

private theorem diagonalLimitObserverDecode_encode_bhist :
    ∀ h : BHist, diagonalLimitObserverDecodeBHist (diagonalLimitObserverEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem diagonalLimitObserver_mk_congr
    {D D' W W' Q Q' T T' S S' R R' H H' C C' P P' N N' : BHist}
    (hD : D' = D) (hW : W' = W) (hQ : Q' = Q) (hT : T' = T) (hS : S' = S)
    (hR : R' = R) (hH : H' = H) (hC : C' = C) (hP : P' = P) (hN : N' = N) :
    DiagonalLimitObserverUp.mk D' W' Q' T' S' R' H' C' P' N' =
      DiagonalLimitObserverUp.mk D W Q T S R H C P N := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hD
  cases hW
  cases hQ
  cases hT
  cases hS
  cases hR
  cases hH
  cases hC
  cases hP
  cases hN
  rfl

def diagonalLimitObserverToEventFlow : DiagonalLimitObserverUp → EventFlow
  | DiagonalLimitObserverUp.mk D W Q T S R H C P N =>
      [[BMark.b0],
        diagonalLimitObserverEncodeBHist D,
        [BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist T,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist R,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        diagonalLimitObserverEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        diagonalLimitObserverEncodeBHist N]

def diagonalLimitObserverFromEventFlow : EventFlow → Option DiagonalLimitObserverUp
  | _tagD :: D :: _tagW :: W :: _tagQ :: Q :: _tagT :: T :: _tagS :: S ::
      _tagR :: R :: _tagH :: H :: _tagC :: C :: _tagP :: P :: _tagN :: N :: [] =>
      some
        (DiagonalLimitObserverUp.mk
          (diagonalLimitObserverDecodeBHist D)
          (diagonalLimitObserverDecodeBHist W)
          (diagonalLimitObserverDecodeBHist Q)
          (diagonalLimitObserverDecodeBHist T)
          (diagonalLimitObserverDecodeBHist S)
          (diagonalLimitObserverDecodeBHist R)
          (diagonalLimitObserverDecodeBHist H)
          (diagonalLimitObserverDecodeBHist C)
          (diagonalLimitObserverDecodeBHist P)
          (diagonalLimitObserverDecodeBHist N))
  | _ => none

private theorem diagonalLimitObserver_round_trip :
    ∀ x : DiagonalLimitObserverUp,
      diagonalLimitObserverFromEventFlow (diagonalLimitObserverToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q T S R H C P N =>
      exact
        congrArg some
          (diagonalLimitObserver_mk_congr
            (diagonalLimitObserverDecode_encode_bhist D)
            (diagonalLimitObserverDecode_encode_bhist W)
            (diagonalLimitObserverDecode_encode_bhist Q)
            (diagonalLimitObserverDecode_encode_bhist T)
            (diagonalLimitObserverDecode_encode_bhist S)
            (diagonalLimitObserverDecode_encode_bhist R)
            (diagonalLimitObserverDecode_encode_bhist H)
            (diagonalLimitObserverDecode_encode_bhist C)
            (diagonalLimitObserverDecode_encode_bhist P)
            (diagonalLimitObserverDecode_encode_bhist N))

private theorem diagonalLimitObserverToEventFlow_injective
    (x y : DiagonalLimitObserverUp) :
    diagonalLimitObserverToEventFlow x = diagonalLimitObserverToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      diagonalLimitObserverFromEventFlow (diagonalLimitObserverToEventFlow x) =
        diagonalLimitObserverFromEventFlow (diagonalLimitObserverToEventFlow y) :=
    congrArg diagonalLimitObserverFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (diagonalLimitObserver_round_trip x).symm
      (Eq.trans hread (diagonalLimitObserver_round_trip y)))

instance diagonalLimitObserverBHistCarrier : BHistCarrier DiagonalLimitObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := diagonalLimitObserverToEventFlow
  fromEventFlow := diagonalLimitObserverFromEventFlow

instance diagonalLimitObserverChapterTasteGate :
    ChapterTasteGate DiagonalLimitObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change diagonalLimitObserverFromEventFlow (diagonalLimitObserverToEventFlow x) = some x
    exact diagonalLimitObserver_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (diagonalLimitObserverToEventFlow_injective x y heq)

def taste_gate : ChapterTasteGate DiagonalLimitObserverUp := by
  -- BEDC touchpoint anchor: BHist BMark
  exact diagonalLimitObserverChapterTasteGate

def diagonalLimitObserverFields : DiagonalLimitObserverUp → List BHist
  | DiagonalLimitObserverUp.mk D W Q T S R H C P N => [D, W, Q, T, S, R, H, C, P, N]

private theorem diagonalLimitObserver_field_faithful_concrete :
    ∀ x y : DiagonalLimitObserverUp, diagonalLimitObserverFields x = diagonalLimitObserverFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D W Q T S R H C P N =>
      cases y with
      | mk D' W' Q' T' S' R' H' C' P' N' =>
          change [D, W, Q, T, S, R, H, C, P, N] = [D', W', Q', T', S', R', H', C', P', N'] at hfields
          injection hfields with hD hTail0
          injection hTail0 with hW hTail1
          injection hTail1 with hQ hTail2
          injection hTail2 with hT hTail3
          injection hTail3 with hS hTail4
          injection hTail4 with hR hTail5
          injection hTail5 with hH hTail6
          injection hTail6 with hC hTail7
          injection hTail7 with hP hTail8
          injection hTail8 with hN _hNil
          cases hD
          cases hW
          cases hQ
          cases hT
          cases hS
          cases hR
          cases hH
          cases hC
          cases hP
          cases hN
          rfl

instance diagonalLimitObserverFieldFaithful :
    FieldFaithful DiagonalLimitObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := diagonalLimitObserverFields
  field_faithful := diagonalLimitObserver_field_faithful_concrete

instance diagonalLimitObserverNontrivial : Nontrivial DiagonalLimitObserverUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DiagonalLimitObserverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DiagonalLimitObserverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

private theorem diagonalLimitObserver_nontrivial_concrete :
    ∃ x y : DiagonalLimitObserverUp, x ≠ y :=
  ⟨DiagonalLimitObserverUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    DiagonalLimitObserverUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
    by
      intro h
      cases h⟩

theorem DiagonalLimitObserverTasteGate_single_carrier_alignment :
    (∀ h : BHist, diagonalLimitObserverDecodeBHist (diagonalLimitObserverEncodeBHist h) = h) ∧
      diagonalLimitObserverEncodeBHist BHist.Empty = ([] : List BMark) ∧
        (∀ x y : DiagonalLimitObserverUp,
          diagonalLimitObserverFields x = diagonalLimitObserverFields y → x = y) ∧
          (∃ x y : DiagonalLimitObserverUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact diagonalLimitObserverDecode_encode_bhist
  · constructor
    · rfl
    · constructor
      · exact diagonalLimitObserver_field_faithful_concrete
      · exact diagonalLimitObserver_nontrivial_concrete

end BEDC.Derived.DiagonalLimitObserverUp
