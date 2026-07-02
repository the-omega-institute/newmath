import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyContinuousFunctionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyContinuousFunctionUp : Type where
  | mk (S R D M U J E H C P N : BHist) : CauchyContinuousFunctionUp
  deriving DecidableEq

def cauchyContinuousFunctionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyContinuousFunctionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyContinuousFunctionEncodeBHist h

def cauchyContinuousFunctionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyContinuousFunctionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyContinuousFunctionDecodeBHist tail)

private theorem CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyContinuousFunctionDecodeBHist
        (cauchyContinuousFunctionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyContinuousFunctionFields :
    CauchyContinuousFunctionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyContinuousFunctionUp.mk S R D M U J E H C P N =>
      [S, R, D, M, U, J, E, H, C, P, N]

def cauchyContinuousFunctionToEventFlow :
    CauchyContinuousFunctionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyContinuousFunctionFields x).map cauchyContinuousFunctionEncodeBHist

private def cauchyContinuousFunctionEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cauchyContinuousFunctionEventAtDefault index rest

def cauchyContinuousFunctionFromEventFlow
    (ef : EventFlow) : Option CauchyContinuousFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyContinuousFunctionUp.mk
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 0 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 1 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 2 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 3 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 4 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 5 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 6 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 7 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 8 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 9 ef))
      (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEventAtDefault 10 ef)))

private theorem CauchyContinuousFunctionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyContinuousFunctionUp,
      cauchyContinuousFunctionFromEventFlow
        (cauchyContinuousFunctionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S R D M U J E H C P N =>
      change
        some
          (CauchyContinuousFunctionUp.mk
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist S))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist R))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist D))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist M))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist U))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist J))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist E))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist H))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist C))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist P))
            (cauchyContinuousFunctionDecodeBHist (cauchyContinuousFunctionEncodeBHist N))) =
          some (CauchyContinuousFunctionUp.mk S R D M U J E H C P N)
      rw [CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode S,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode R,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode D,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode M,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode U,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode J,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode E,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode H,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode C,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode P,
        CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode N]

private theorem CauchyContinuousFunctionTasteGate_single_carrier_alignment_injective
    {x y : CauchyContinuousFunctionUp} :
    cauchyContinuousFunctionToEventFlow x =
      cauchyContinuousFunctionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyContinuousFunctionFromEventFlow
          (cauchyContinuousFunctionToEventFlow x) =
        cauchyContinuousFunctionFromEventFlow
          (cauchyContinuousFunctionToEventFlow y) :=
    congrArg cauchyContinuousFunctionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyContinuousFunctionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyContinuousFunctionTasteGate_single_carrier_alignment_round_trip y)))

private theorem CauchyContinuousFunctionTasteGate_single_carrier_alignment_fields :
    ∀ x y : CauchyContinuousFunctionUp,
      cauchyContinuousFunctionFields x = cauchyContinuousFunctionFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 R1 D1 M1 U1 J1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 R2 D2 M2 U2 J2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance cauchyContinuousFunctionBHistCarrier :
    BHistCarrier CauchyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyContinuousFunctionToEventFlow
  fromEventFlow := cauchyContinuousFunctionFromEventFlow

instance cauchyContinuousFunctionChapterTasteGate :
    ChapterTasteGate CauchyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyContinuousFunctionFromEventFlow
        (cauchyContinuousFunctionToEventFlow x) = some x
    exact CauchyContinuousFunctionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyContinuousFunctionTasteGate_single_carrier_alignment_injective heq)

instance cauchyContinuousFunctionFieldFaithful :
    FieldFaithful CauchyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyContinuousFunctionFields
  field_faithful := CauchyContinuousFunctionTasteGate_single_carrier_alignment_fields

instance cauchyContinuousFunctionNontrivial :
    Nontrivial CauchyContinuousFunctionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyContinuousFunctionUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyContinuousFunctionUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyContinuousFunctionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyContinuousFunctionChapterTasteGate

theorem CauchyContinuousFunctionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyContinuousFunctionDecodeBHist
        (cauchyContinuousFunctionEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyContinuousFunctionUp) ∧
        Nonempty (ChapterTasteGate CauchyContinuousFunctionUp) ∧
          Nonempty (FieldFaithful CauchyContinuousFunctionUp) ∧
            cauchyContinuousFunctionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨CauchyContinuousFunctionTasteGate_single_carrier_alignment_decode,
      ⟨cauchyContinuousFunctionBHistCarrier⟩,
      ⟨cauchyContinuousFunctionChapterTasteGate⟩,
      ⟨cauchyContinuousFunctionFieldFaithful⟩,
      rfl⟩

end BEDC.Derived.CauchyContinuousFunctionUp
