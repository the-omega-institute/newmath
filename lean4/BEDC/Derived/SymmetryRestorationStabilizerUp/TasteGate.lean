import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SymmetryRestorationStabilizerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SymmetryRestorationStabilizerUp : Type where
  | mk (Q A T U M O R H C P N : BHist) : SymmetryRestorationStabilizerUp
  deriving DecidableEq

def symmetryRestorationStabilizerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: symmetryRestorationStabilizerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: symmetryRestorationStabilizerEncodeBHist h

def symmetryRestorationStabilizerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (symmetryRestorationStabilizerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (symmetryRestorationStabilizerDecodeBHist tail)

private theorem SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      symmetryRestorationStabilizerDecodeBHist
          (symmetryRestorationStabilizerEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def symmetryRestorationStabilizerFields :
    SymmetryRestorationStabilizerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SymmetryRestorationStabilizerUp.mk Q A T U M O R H C P N =>
      [Q, A, T, U, M, O, R, H, C, P, N]

def symmetryRestorationStabilizerToEventFlow :
    SymmetryRestorationStabilizerUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (symmetryRestorationStabilizerFields x).map
      symmetryRestorationStabilizerEncodeBHist

private def symmetryRestorationStabilizerEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      symmetryRestorationStabilizerEventAtDefault index rest

def symmetryRestorationStabilizerFromEventFlow
    (flow : EventFlow) : Option SymmetryRestorationStabilizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (SymmetryRestorationStabilizerUp.mk
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 0 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 1 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 2 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 3 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 4 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 5 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 6 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 7 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 8 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 9 flow))
      (symmetryRestorationStabilizerDecodeBHist
        (symmetryRestorationStabilizerEventAtDefault 10 flow)))

private theorem SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_round_trip :
    ∀ x : SymmetryRestorationStabilizerUp,
      symmetryRestorationStabilizerFromEventFlow
          (symmetryRestorationStabilizerToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk Q A T U M O R H C P N =>
      change
        some
            (SymmetryRestorationStabilizerUp.mk
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist Q))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist A))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist T))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist U))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist M))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist O))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist R))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist H))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist C))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist P))
              (symmetryRestorationStabilizerDecodeBHist
                (symmetryRestorationStabilizerEncodeBHist N))) =
          some (SymmetryRestorationStabilizerUp.mk Q A T U M O R H C P N)
      rw [SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode Q,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode A,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode T,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode U,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode M,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode O,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode R,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode H,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode C,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode P,
        SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode N]

private theorem SymmetryRestorationStabilizerToEventFlow_injective
    {x y : SymmetryRestorationStabilizerUp} :
    symmetryRestorationStabilizerToEventFlow x =
        symmetryRestorationStabilizerToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hread :
      symmetryRestorationStabilizerFromEventFlow
          (symmetryRestorationStabilizerToEventFlow x) =
        symmetryRestorationStabilizerFromEventFlow
          (symmetryRestorationStabilizerToEventFlow y) :=
    congrArg symmetryRestorationStabilizerFromEventFlow hxy
  exact Option.some.inj
    (Eq.trans
      (SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_round_trip y)))

private theorem SymmetryRestorationStabilizer_field_faithful :
    ∀ x y : SymmetryRestorationStabilizerUp,
      symmetryRestorationStabilizerFields x =
          symmetryRestorationStabilizerFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk Q1 A1 T1 U1 M1 O1 R1 H1 C1 P1 N1 =>
      cases y with
      | mk Q2 A2 T2 U2 M2 O2 R2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance symmetryRestorationStabilizerBHistCarrier :
    BHistCarrier SymmetryRestorationStabilizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := symmetryRestorationStabilizerToEventFlow
  fromEventFlow := symmetryRestorationStabilizerFromEventFlow

instance symmetryRestorationStabilizerChapterTasteGate :
    ChapterTasteGate SymmetryRestorationStabilizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      symmetryRestorationStabilizerFromEventFlow
          (symmetryRestorationStabilizerToEventFlow x) =
        some x
    exact SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (SymmetryRestorationStabilizerToEventFlow_injective heq)

instance symmetryRestorationStabilizerFieldFaithful :
    FieldFaithful SymmetryRestorationStabilizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := symmetryRestorationStabilizerFields
  field_faithful := SymmetryRestorationStabilizer_field_faithful

instance symmetryRestorationStabilizerNontrivial :
    Nontrivial SymmetryRestorationStabilizerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨SymmetryRestorationStabilizerUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      SymmetryRestorationStabilizerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SymmetryRestorationStabilizerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  symmetryRestorationStabilizerChapterTasteGate

theorem SymmetryRestorationStabilizerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      symmetryRestorationStabilizerDecodeBHist
          (symmetryRestorationStabilizerEncodeBHist h) =
        h) ∧
      Nonempty (BHistCarrier SymmetryRestorationStabilizerUp) ∧
        Nonempty (ChapterTasteGate SymmetryRestorationStabilizerUp) ∧
          Nonempty (FieldFaithful SymmetryRestorationStabilizerUp) ∧
            Nonempty (BEDC.Meta.TasteGate.Nontrivial SymmetryRestorationStabilizerUp) ∧
              symmetryRestorationStabilizerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨SymmetryRestorationStabilizerTasteGate_single_carrier_alignment_decode,
      ⟨symmetryRestorationStabilizerBHistCarrier⟩,
      ⟨symmetryRestorationStabilizerChapterTasteGate⟩,
      ⟨symmetryRestorationStabilizerFieldFaithful⟩,
      ⟨symmetryRestorationStabilizerNontrivial⟩,
      rfl⟩

end BEDC.Derived.SymmetryRestorationStabilizerUp
