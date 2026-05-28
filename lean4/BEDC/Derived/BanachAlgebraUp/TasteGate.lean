import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BanachAlgebraUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive BanachAlgebraUp : Type where
  | mk (R N B Q M H C P L : BHist) : BanachAlgebraUp
  deriving DecidableEq

def banachAlgebraEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: banachAlgebraEncodeBHist h
  | BHist.e1 h => BMark.b1 :: banachAlgebraEncodeBHist h

def banachAlgebraDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (banachAlgebraDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (banachAlgebraDecodeBHist tail)

private theorem BanachAlgebraTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, banachAlgebraDecodeBHist (banachAlgebraEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def banachAlgebraToEventFlow : BanachAlgebraUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BanachAlgebraUp.mk R N B Q M H C P L =>
      [[BMark.b0],
        banachAlgebraEncodeBHist R,
        [BMark.b1, BMark.b0],
        banachAlgebraEncodeBHist N,
        [BMark.b1, BMark.b1, BMark.b0],
        banachAlgebraEncodeBHist B,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachAlgebraEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachAlgebraEncodeBHist M,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachAlgebraEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        banachAlgebraEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        banachAlgebraEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        banachAlgebraEncodeBHist L]

private def banachAlgebraEventAtDefault : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => banachAlgebraEventAtDefault index rest

def banachAlgebraFromEventFlow (ef : EventFlow) : Option BanachAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BanachAlgebraUp.mk
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 1 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 3 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 5 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 7 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 9 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 11 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 13 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 15 ef))
      (banachAlgebraDecodeBHist (banachAlgebraEventAtDefault 17 ef)))

private theorem BanachAlgebraTasteGate_single_carrier_alignment_round_trip :
    ∀ x : BanachAlgebraUp,
      banachAlgebraFromEventFlow (banachAlgebraToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R N B Q M H C P L =>
      change
        some
          (BanachAlgebraUp.mk
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist R))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist N))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist B))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist Q))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist M))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist H))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist C))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist P))
            (banachAlgebraDecodeBHist (banachAlgebraEncodeBHist L))) =
          some (BanachAlgebraUp.mk R N B Q M H C P L)
      rw [BanachAlgebraTasteGate_single_carrier_alignment_decode R,
        BanachAlgebraTasteGate_single_carrier_alignment_decode N,
        BanachAlgebraTasteGate_single_carrier_alignment_decode B,
        BanachAlgebraTasteGate_single_carrier_alignment_decode Q,
        BanachAlgebraTasteGate_single_carrier_alignment_decode M,
        BanachAlgebraTasteGate_single_carrier_alignment_decode H,
        BanachAlgebraTasteGate_single_carrier_alignment_decode C,
        BanachAlgebraTasteGate_single_carrier_alignment_decode P,
        BanachAlgebraTasteGate_single_carrier_alignment_decode L]

private theorem BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : BanachAlgebraUp} :
    banachAlgebraToEventFlow x = banachAlgebraToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      banachAlgebraFromEventFlow (banachAlgebraToEventFlow x) =
        banachAlgebraFromEventFlow (banachAlgebraToEventFlow y) :=
    congrArg banachAlgebraFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (BanachAlgebraTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (BanachAlgebraTasteGate_single_carrier_alignment_round_trip y)))

private def banachAlgebraFields : BanachAlgebraUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BanachAlgebraUp.mk R N B Q M H C P L => [R, N, B, Q, M, H, C, P, L]

private theorem BanachAlgebraTasteGate_single_carrier_alignment_fields :
    ∀ x y : BanachAlgebraUp, banachAlgebraFields x = banachAlgebraFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R1 N1 B1 Q1 M1 H1 C1 P1 L1 =>
      cases y with
      | mk R2 N2 B2 Q2 M2 H2 C2 P2 L2 =>
          cases hfields
          rfl

instance banachAlgebraBHistCarrier : BHistCarrier BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := banachAlgebraToEventFlow
  fromEventFlow := banachAlgebraFromEventFlow

instance banachAlgebraChapterTasteGate : ChapterTasteGate BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change banachAlgebraFromEventFlow (banachAlgebraToEventFlow x) = some x
    exact BanachAlgebraTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (BanachAlgebraTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance banachAlgebraFieldFaithful : FieldFaithful BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := banachAlgebraFields
  field_faithful := BanachAlgebraTasteGate_single_carrier_alignment_fields

instance banachAlgebraNontrivial : Nontrivial BanachAlgebraUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BanachAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BanachAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BanachAlgebraUp :=
  -- BEDC touchpoint anchor: BHist BMark
  banachAlgebraChapterTasteGate

theorem BanachAlgebraTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate BanachAlgebraUp) ∧
      (∀ x : BanachAlgebraUp, ∃ e : EventFlow, BHistCarrier.fromEventFlow e = some x) ∧
        (∃ x y : BanachAlgebraUp,
          x =
            BanachAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
          y =
            BanachAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ∧
          x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  constructor
  · exact ⟨banachAlgebraChapterTasteGate⟩
  · constructor
    · exact ChapterTasteGate.no_hidden_input
    · refine
        ⟨BanachAlgebraUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
          BanachAlgebraUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, ?_⟩
      constructor
      · rfl
      · constructor
        · rfl
        · intro h
          cases h

end BEDC.Derived.BanachAlgebraUp.TasteGate
