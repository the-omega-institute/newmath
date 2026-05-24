import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyProductCommutativityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyProductCommutativityUp : Type where
  | mk (Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N : BHist) :
      CauchyProductCommutativityUp
  deriving DecidableEq

def cauchyProductCommutativityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyProductCommutativityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyProductCommutativityEncodeBHist h

def cauchyProductCommutativityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyProductCommutativityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyProductCommutativityDecodeBHist tail)

private theorem CauchyProductCommutativityTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyProductCommutativityDecodeBHist
          (cauchyProductCommutativityEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyProductCommutativityFields :
    CauchyProductCommutativityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N =>
      [Pxy, Pyx, Wx, Wy, Dxy, Dyx, Rxy, Ryx, Exy, Eyx, H, C, Q, N]

def cauchyProductCommutativityToEventFlow :
    CauchyProductCommutativityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N =>
      [cauchyProductCommutativityEncodeBHist Pxy,
        cauchyProductCommutativityEncodeBHist Pyx,
        cauchyProductCommutativityEncodeBHist Wx,
        cauchyProductCommutativityEncodeBHist Wy,
        cauchyProductCommutativityEncodeBHist Dxy,
        cauchyProductCommutativityEncodeBHist Dyx,
        cauchyProductCommutativityEncodeBHist Rxy,
        cauchyProductCommutativityEncodeBHist Ryx,
        cauchyProductCommutativityEncodeBHist Exy,
        cauchyProductCommutativityEncodeBHist Eyx,
        cauchyProductCommutativityEncodeBHist H,
        cauchyProductCommutativityEncodeBHist C,
        cauchyProductCommutativityEncodeBHist Q,
        cauchyProductCommutativityEncodeBHist N]

private def cauchyProductCommutativityEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyProductCommutativityEventAtDefault index rest

def cauchyProductCommutativityFromEventFlow
    (ef : EventFlow) : Option CauchyProductCommutativityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyProductCommutativityUp.mk
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 0 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 1 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 2 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 3 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 4 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 5 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 6 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 7 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 8 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 9 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 10 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 11 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 12 ef))
      (cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEventAtDefault 13 ef)))

private theorem CauchyProductCommutativityTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyProductCommutativityUp,
      cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy Eyx H C Q N =>
      change
        some
          (CauchyProductCommutativityUp.mk
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Pxy))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Pyx))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Wx))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Wy))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Dxy))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Dyx))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Rxy))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Ryx))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Exy))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Eyx))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist H))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist C))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist Q))
            (cauchyProductCommutativityDecodeBHist
              (cauchyProductCommutativityEncodeBHist N))) =
          some
            (CauchyProductCommutativityUp.mk Pxy Pyx Wx Wy Dxy Dyx Rxy Ryx Exy
              Eyx H C Q N)
      rw [CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Pxy,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Pyx,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Wx,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Wy,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Dxy,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Dyx,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Rxy,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Ryx,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Exy,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Eyx,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode H,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode C,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode Q,
        CauchyProductCommutativityTasteGate_single_carrier_alignment_decode N]

private theorem CauchyProductCommutativityTasteGate_single_carrier_alignment_injective
    {x y : CauchyProductCommutativityUp} :
    cauchyProductCommutativityToEventFlow x = cauchyProductCommutativityToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow x) =
        cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow y) :=
    congrArg cauchyProductCommutativityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyProductCommutativityTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyProductCommutativityTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyProductCommutativityFields_faithful :
    ∀ x y : CauchyProductCommutativityUp,
      cauchyProductCommutativityFields x = cauchyProductCommutativityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Pxy₁ Pyx₁ Wx₁ Wy₁ Dxy₁ Dyx₁ Rxy₁ Ryx₁ Exy₁ Eyx₁ H₁ C₁ Q₁ N₁ =>
      cases y with
      | mk Pxy₂ Pyx₂ Wx₂ Wy₂ Dxy₂ Dyx₂ Rxy₂ Ryx₂ Exy₂ Eyx₂ H₂ C₂ Q₂ N₂ =>
          cases hfields
          rfl

instance cauchyProductCommutativityBHistCarrier :
    BHistCarrier CauchyProductCommutativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyProductCommutativityToEventFlow
  fromEventFlow := cauchyProductCommutativityFromEventFlow

instance cauchyProductCommutativityChapterTasteGate :
    ChapterTasteGate CauchyProductCommutativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow x) =
        some x
    exact CauchyProductCommutativityTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyProductCommutativityTasteGate_single_carrier_alignment_injective heq)

instance cauchyProductCommutativityFieldFaithful :
    FieldFaithful CauchyProductCommutativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyProductCommutativityFields
  field_faithful := cauchyProductCommutativityFields_faithful

instance cauchyProductCommutativityNontrivial :
    Nontrivial CauchyProductCommutativityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyProductCommutativityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyProductCommutativityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CauchyProductCommutativityTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CauchyProductCommutativityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyProductCommutativityChapterTasteGate

theorem CauchyProductCommutativityTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyProductCommutativityDecodeBHist
        (cauchyProductCommutativityEncodeBHist h) = h) ∧
      (∀ x : CauchyProductCommutativityUp,
        cauchyProductCommutativityFromEventFlow
          (cauchyProductCommutativityToEventFlow x) = some x) ∧
      (∀ x y : CauchyProductCommutativityUp,
        cauchyProductCommutativityToEventFlow x =
            cauchyProductCommutativityToEventFlow y →
          x = y) ∧
      cauchyProductCommutativityEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyProductCommutativityTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyProductCommutativityTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact CauchyProductCommutativityTasteGate_single_carrier_alignment_injective heq
  · rfl

end BEDC.Derived.CauchyProductCommutativityUp
