import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyFieldDistributivityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyFieldDistributivityUp : Type where
  | mk
      (X Y Z W DX DY DZ SL ML MY MZ SR EL ER R H C P N : BHist) :
      RegularCauchyFieldDistributivityUp
  deriving DecidableEq

def regularCauchyFieldDistributivityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyFieldDistributivityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyFieldDistributivityEncodeBHist h

def regularCauchyFieldDistributivityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyFieldDistributivityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyFieldDistributivityDecodeBHist tail)

private theorem
    RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyFieldDistributivityDecodeBHist
          (regularCauchyFieldDistributivityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyFieldDistributivityFields :
    RegularCauchyFieldDistributivityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyFieldDistributivityUp.mk X Y Z W DX DY DZ SL ML MY MZ SR EL ER R H C P N =>
      [X, Y, Z, W, DX, DY, DZ, SL, ML, MY, MZ, SR, EL, ER, R, H, C, P, N]

def regularCauchyFieldDistributivityToEventFlow :
    RegularCauchyFieldDistributivityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      List.map regularCauchyFieldDistributivityEncodeBHist
        (regularCauchyFieldDistributivityFields x)

private def regularCauchyFieldDistributivityRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyFieldDistributivityRawAt index rest

def regularCauchyFieldDistributivityFromEventFlow
    (flow : EventFlow) : Option RegularCauchyFieldDistributivityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyFieldDistributivityUp.mk
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 0 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 1 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 2 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 3 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 4 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 5 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 6 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 7 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 8 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 9 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 10 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 11 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 12 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 13 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 14 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 15 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 16 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 17 flow))
      (regularCauchyFieldDistributivityDecodeBHist
        (regularCauchyFieldDistributivityRawAt 18 flow)))

private theorem RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyFieldDistributivityUp,
      regularCauchyFieldDistributivityFromEventFlow
          (regularCauchyFieldDistributivityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X Y Z W DX DY DZ SL ML MY MZ SR EL ER R H C P N =>
      change
        some
          (RegularCauchyFieldDistributivityUp.mk
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist X))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist Y))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist Z))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist W))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist DX))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist DY))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist DZ))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist SL))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist ML))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist MY))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist MZ))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist SR))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist EL))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist ER))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist R))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist H))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist C))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist P))
            (regularCauchyFieldDistributivityDecodeBHist
              (regularCauchyFieldDistributivityEncodeBHist N))) =
          some
            (RegularCauchyFieldDistributivityUp.mk X Y Z W DX DY DZ SL ML MY MZ SR EL ER R H C P N)
      rw [
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode X,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode Y,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode Z,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode DX,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode DY,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode DZ,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode SL,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode ML,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode MY,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode MZ,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode SR,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode EL,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode ER,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode R,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode N]

private theorem
    RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyFieldDistributivityUp} :
    regularCauchyFieldDistributivityToEventFlow x =
        regularCauchyFieldDistributivityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyFieldDistributivityFromEventFlow
          (regularCauchyFieldDistributivityToEventFlow x) =
        regularCauchyFieldDistributivityFromEventFlow
          (regularCauchyFieldDistributivityToEventFlow y) :=
    congrArg regularCauchyFieldDistributivityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_round_trip y)))

private theorem regularCauchyFieldDistributivityFieldsFaithful :
    ∀ x y : RegularCauchyFieldDistributivityUp,
      regularCauchyFieldDistributivityFields x =
          regularCauchyFieldDistributivityFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x
  cases y
  cases hfields
  rfl

instance regularCauchyFieldDistributivityBHistCarrier :
    BHistCarrier RegularCauchyFieldDistributivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyFieldDistributivityToEventFlow
  fromEventFlow := regularCauchyFieldDistributivityFromEventFlow

instance regularCauchyFieldDistributivityChapterTasteGate :
    ChapterTasteGate RegularCauchyFieldDistributivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyFieldDistributivityFromEventFlow
          (regularCauchyFieldDistributivityToEventFlow x) =
        some x
    exact RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance regularCauchyFieldDistributivityFieldFaithful :
    FieldFaithful RegularCauchyFieldDistributivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyFieldDistributivityFields
  field_faithful := regularCauchyFieldDistributivityFieldsFaithful

instance regularCauchyFieldDistributivityNontrivial :
    Nontrivial RegularCauchyFieldDistributivityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyFieldDistributivityUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyFieldDistributivityUp.mk
        (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyFieldDistributivityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyFieldDistributivityChapterTasteGate

theorem RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment :
    (forall h : BHist,
      regularCauchyFieldDistributivityDecodeBHist
          (regularCauchyFieldDistributivityEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier RegularCauchyFieldDistributivityUp) ∧
      Nonempty (ChapterTasteGate RegularCauchyFieldDistributivityUp) ∧
      regularCauchyFieldDistributivityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyFieldDistributivityTasteGate_single_carrier_alignment_decode_encode,
      Nonempty.intro regularCauchyFieldDistributivityBHistCarrier,
      Nonempty.intro regularCauchyFieldDistributivityChapterTasteGate,
      rfl⟩

end BEDC.Derived.RegularCauchyFieldDistributivityUp
