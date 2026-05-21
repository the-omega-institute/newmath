import BEDC.Derived.DyadicSplineUp
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicSplineUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicSplineUp : Type where
  | mk (k a l i q r h c p n : BHist) : DyadicSplineUp
  deriving DecidableEq

def DyadicSplineTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: DyadicSplineTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: DyadicSplineTasteGate_single_carrier_alignment_encodeBHist h

def DyadicSplineTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DyadicSplineTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DyadicSplineTasteGate_single_carrier_alignment_decodeBHist
          (DyadicSplineTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DyadicSplineTasteGate_single_carrier_alignment_fields : DyadicSplineUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicSplineUp.mk k a l i q r h c p n => [k, a, l, i, q, r, h, c, p, n]

def DyadicSplineTasteGate_single_carrier_alignment_toEventFlow :
    DyadicSplineUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (DyadicSplineTasteGate_single_carrier_alignment_fields x).map
      DyadicSplineTasteGate_single_carrier_alignment_encodeBHist

def DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DyadicSplineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | k :: a :: l :: i :: q :: r :: h :: c :: p :: n :: [] =>
      some
        (DyadicSplineUp.mk
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist k)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist a)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist l)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist i)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist q)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist r)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist h)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist c)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist p)
          (DyadicSplineTasteGate_single_carrier_alignment_decodeBHist n))
  | _ => none

private theorem DyadicSplineTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicSplineUp,
      DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicSplineTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk k a l i q r h c p n =>
      simp only [DyadicSplineTasteGate_single_carrier_alignment_toEventFlow,
        DyadicSplineTasteGate_single_carrier_alignment_fields,
        DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow, List.map_cons,
        List.map_nil, DyadicSplineTasteGate_single_carrier_alignment_decode_encode]

private theorem DyadicSplineTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicSplineUp} :
    DyadicSplineTasteGate_single_carrier_alignment_toEventFlow x =
        DyadicSplineTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicSplineTasteGate_single_carrier_alignment_toEventFlow x) =
        DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicSplineTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicSplineTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicSplineTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicSplineTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DyadicSplineUp,
      DyadicSplineTasteGate_single_carrier_alignment_fields x =
          DyadicSplineTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk k₁ a₁ l₁ i₁ q₁ r₁ h₁ c₁ p₁ n₁ =>
      cases y with
      | mk k₂ a₂ l₂ i₂ q₂ r₂ h₂ c₂ p₂ n₂ =>
          injection hfields with hk tail0
          injection tail0 with ha tail1
          injection tail1 with hl tail2
          injection tail2 with hi tail3
          injection tail3 with hq tail4
          injection tail4 with hr tail5
          injection tail5 with hh tail6
          injection tail6 with hc tail7
          injection tail7 with hp tail8
          injection tail8 with hn _
          subst hk
          subst ha
          subst hl
          subst hi
          subst hq
          subst hr
          subst hh
          subst hc
          subst hp
          subst hn
          rfl

instance DyadicSplineTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DyadicSplineTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow

instance DyadicSplineTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DyadicSplineTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicSplineTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DyadicSplineTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicSplineTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance DyadicSplineTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DyadicSplineTasteGate_single_carrier_alignment_fields
  field_faithful := DyadicSplineTasteGate_single_carrier_alignment_fields_faithful

instance DyadicSplineTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial DyadicSplineUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicSplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicSplineUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicSplineUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DyadicSplineTasteGate_single_carrier_alignment_ChapterTasteGate

theorem DyadicSplineTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      DyadicSplineTasteGate_single_carrier_alignment_decodeBHist
          (DyadicSplineTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      DyadicSplineTasteGate_single_carrier_alignment_fields
          (DyadicSplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] ∧
        DyadicSplineTasteGate_single_carrier_alignment_toEventFlow
          (DyadicSplineUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  constructor
  · exact DyadicSplineTasteGate_single_carrier_alignment_decode_encode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.DyadicSplineUp.TasteGate
