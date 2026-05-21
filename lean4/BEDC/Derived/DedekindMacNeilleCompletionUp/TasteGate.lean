import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DedekindMacNeilleCompletionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DedekindMacNeilleCompletionUp : Type where
  | mk (L U K Q E H C P N : BHist) : DedekindMacNeilleCompletionUp
  deriving DecidableEq

def DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b1, BMark.b1, BMark.b0]

def DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist h

def DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fields :
    DedekindMacNeilleCompletionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindMacNeilleCompletionUp.mk L U K Q E H C P N => [L, U, K, Q, E, H, C, P, N]

def DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow :
    DedekindMacNeilleCompletionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DedekindMacNeilleCompletionUp.mk L U K Q E H C P N =>
      [DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_tag,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist L,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist U,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist K,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist Q,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist E,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist H,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist C,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist P,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist N]

private def DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt index rest

def DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option DedekindMacNeilleCompletionUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (DedekindMacNeilleCompletionUp.mk
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 1 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 2 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 3 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 4 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 5 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 6 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 7 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 8 ef))
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_eventAt 9 ef)))

private theorem DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DedekindMacNeilleCompletionUp,
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk L U K Q E H C P N =>
      change
        some
          (DedekindMacNeilleCompletionUp.mk
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist L))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist U))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist K))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist Q))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist E))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist H))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist C))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist P))
            (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
              (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (DedekindMacNeilleCompletionUp.mk L U K Q E H C P N)
      rw [DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode L,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode U,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode K,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode Q,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode E,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode H,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode C,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode P,
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode N]

private theorem DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_injective
    {x y : DedekindMacNeilleCompletionUp} :
    DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow x =
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_round_trip y)))

private theorem DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : DedekindMacNeilleCompletionUp,
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fields x =
          DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ U₁ K₁ Q₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ U₂ K₂ Q₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fromEventFlow

instance DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fromEventFlow
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_injective heq)

instance DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fields
  field_faithful :=
    DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fields_faithful

instance DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial DedekindMacNeilleCompletionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DedekindMacNeilleCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DedekindMacNeilleCompletionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DedekindMacNeilleCompletionTasteGate_single_carrier_alignment :
    (forall h : BHist,
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decodeBHist
          (DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_encodeBHist h) =
        h) /\
      DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_fields
          (DedekindMacNeilleCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] /\
        DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_toEventFlow
            (DedekindMacNeilleCompletionUp.mk BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
          [[BMark.b1, BMark.b1, BMark.b0], [], [], [], [], [], [], [], [], []] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact DedekindMacNeilleCompletionTasteGate_single_carrier_alignment_decode
  · constructor
    · rfl
    · rfl

end BEDC.Derived.DedekindMacNeilleCompletionUp
