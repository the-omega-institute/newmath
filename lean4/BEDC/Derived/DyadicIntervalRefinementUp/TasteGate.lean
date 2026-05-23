import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicIntervalRefinementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicIntervalRefinementUp : Type where
  | mk : (parent childLeft childRight endpointReuse refinement window readback : BHist) →
      DyadicIntervalRefinementUp
  deriving DecidableEq

def DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist h

def DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields :
    DyadicIntervalRefinementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicIntervalRefinementUp.mk parent childLeft childRight endpointReuse refinement window
      readback =>
      [parent, childLeft, childRight, endpointReuse, refinement, window, readback]

def DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow :
    DyadicIntervalRefinementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      [BMark.b1, BMark.b1, BMark.b0, BMark.b0] ::
        (DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields x).map
          DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist

def DyadicIntervalRefinementTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DyadicIntervalRefinementUp
  -- BEDC touchpoint anchor: BHist BMark
  | _tag :: parent :: childLeft :: childRight :: endpointReuse :: refinement :: window ::
      readback :: [] =>
      some
        (DyadicIntervalRefinementUp.mk
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist parent)
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist childLeft)
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist childRight)
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist endpointReuse)
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist refinement)
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist window)
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist readback))
  | _ => none

private theorem DyadicIntervalRefinementTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DyadicIntervalRefinementUp,
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk parent childLeft childRight endpointReuse refinement window readback =>
      change
        some
          (DyadicIntervalRefinementUp.mk
            (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist parent))
            (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist childLeft))
            (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist childRight))
            (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist endpointReuse))
            (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist refinement))
            (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist window))
            (DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
              (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist readback))) =
          some
            (DyadicIntervalRefinementUp.mk parent childLeft childRight endpointReuse refinement window
              readback)
      rw [DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode parent,
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode childLeft,
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode childRight,
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode endpointReuse,
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode refinement,
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode window,
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode readback]

private theorem DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicIntervalRefinementUp} :
    DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow x =
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow y →
    x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow x) =
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DyadicIntervalRefinementTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicIntervalRefinementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DyadicIntervalRefinementTasteGate_single_carrier_alignment_round_trip y)))

private theorem DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DyadicIntervalRefinementUp,
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields x =
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk parent₁ childLeft₁ childRight₁ endpointReuse₁ refinement₁ window₁ readback₁ =>
      cases y with
      | mk parent₂ childLeft₂ childRight₂ endpointReuse₂ refinement₂ window₂ readback₂ =>
          injection hfields with hparent tail1
          injection tail1 with hchildLeft tail2
          injection tail2 with hchildRight tail3
          injection tail3 with hendpointReuse tail4
          injection tail4 with hrefinement tail5
          injection tail5 with hwindow tail6
          injection tail6 with hreadback _
          subst hparent
          subst hchildLeft
          subst hchildRight
          subst hendpointReuse
          subst hrefinement
          subst hwindow
          subst hreadback
          rfl

instance dyadicIntervalRefinementBHistCarrier :
    BHistCarrier DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DyadicIntervalRefinementTasteGate_single_carrier_alignment_fromEventFlow

instance dyadicIntervalRefinementChapterTasteGate :
    ChapterTasteGate DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_fromEventFlow
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DyadicIntervalRefinementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicIntervalRefinementFieldFaithful :
    FieldFaithful DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields
  field_faithful :=
    DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields_faithful

instance dyadicIntervalRefinementNontrivial : Nontrivial DyadicIntervalRefinementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicIntervalRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      DyadicIntervalRefinementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hparent
        cases hparent⟩

def taste_gate : ChapterTasteGate DyadicIntervalRefinementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicIntervalRefinementChapterTasteGate

theorem DyadicIntervalRefinementTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_decodeBHist
          (DyadicIntervalRefinementTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      DyadicIntervalRefinementTasteGate_single_carrier_alignment_fields
          (DyadicIntervalRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty] ∧
        DyadicIntervalRefinementTasteGate_single_carrier_alignment_toEventFlow
            (DyadicIntervalRefinementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b1, BMark.b0, BMark.b0], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨DyadicIntervalRefinementTasteGate_single_carrier_alignment_decode_encode, rfl, rfl⟩

end BEDC.Derived.DyadicIntervalRefinementUp
