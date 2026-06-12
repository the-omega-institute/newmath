import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DvoretzkyFiniteDimensionalSectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DvoretzkyFiniteDimensionalSectionUp : Type where
  | mk (V N I M E D H C P Q : BHist) : DvoretzkyFiniteDimensionalSectionUp
  deriving DecidableEq

def dvoretzkyFiniteDimensionalSectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dvoretzkyFiniteDimensionalSectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dvoretzkyFiniteDimensionalSectionEncodeBHist h

def dvoretzkyFiniteDimensionalSectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dvoretzkyFiniteDimensionalSectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dvoretzkyFiniteDimensionalSectionDecodeBHist tail)

private theorem DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      dvoretzkyFiniteDimensionalSectionDecodeBHist
          (dvoretzkyFiniteDimensionalSectionEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dvoretzkyFiniteDimensionalSectionFields :
    DvoretzkyFiniteDimensionalSectionUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DvoretzkyFiniteDimensionalSectionUp.mk V N I M E D H C P Q =>
      [V, N, I, M, E, D, H, C, P, Q]

def dvoretzkyFiniteDimensionalSectionToEventFlow :
    DvoretzkyFiniteDimensionalSectionUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (dvoretzkyFiniteDimensionalSectionFields x).map
      dvoretzkyFiniteDimensionalSectionEncodeBHist

private def dvoretzkyFiniteDimensionalSectionEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => dvoretzkyFiniteDimensionalSectionEventAtDefault index rest

def dvoretzkyFiniteDimensionalSectionFromEventFlow
    (ef : EventFlow) : Option DvoretzkyFiniteDimensionalSectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (DvoretzkyFiniteDimensionalSectionUp.mk
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 0 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 1 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 2 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 3 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 4 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 5 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 6 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 7 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 8 ef))
      (dvoretzkyFiniteDimensionalSectionDecodeBHist
        (dvoretzkyFiniteDimensionalSectionEventAtDefault 9 ef)))

private theorem DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_round_trip :
    ∀ x : DvoretzkyFiniteDimensionalSectionUp,
      dvoretzkyFiniteDimensionalSectionFromEventFlow
          (dvoretzkyFiniteDimensionalSectionToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk V N I M E D H C P Q =>
      change
        some
          (DvoretzkyFiniteDimensionalSectionUp.mk
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist V))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist N))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist I))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist M))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist E))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist D))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist H))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist C))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist P))
            (dvoretzkyFiniteDimensionalSectionDecodeBHist
              (dvoretzkyFiniteDimensionalSectionEncodeBHist Q))) =
          some (DvoretzkyFiniteDimensionalSectionUp.mk V N I M E D H C P Q)
      rw [DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode V,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode N,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode I,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode M,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode E,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode D,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode H,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode C,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode P,
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode Q]

private theorem DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_injective
    {x y : DvoretzkyFiniteDimensionalSectionUp} :
    dvoretzkyFiniteDimensionalSectionToEventFlow x =
        dvoretzkyFiniteDimensionalSectionToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dvoretzkyFiniteDimensionalSectionFromEventFlow
          (dvoretzkyFiniteDimensionalSectionToEventFlow x) =
        dvoretzkyFiniteDimensionalSectionFromEventFlow
          (dvoretzkyFiniteDimensionalSectionToEventFlow y) :=
    congrArg dvoretzkyFiniteDimensionalSectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_round_trip y)))

private theorem DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_fields :
    ∀ x y : DvoretzkyFiniteDimensionalSectionUp,
      dvoretzkyFiniteDimensionalSectionFields x =
        dvoretzkyFiniteDimensionalSectionFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk V1 N1 I1 M1 E1 D1 H1 C1 P1 Q1 =>
      cases y with
      | mk V2 N2 I2 M2 E2 D2 H2 C2 P2 Q2 =>
          cases hfields
          rfl

instance dvoretzkyFiniteDimensionalSectionBHistCarrier :
    BHistCarrier DvoretzkyFiniteDimensionalSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dvoretzkyFiniteDimensionalSectionToEventFlow
  fromEventFlow := dvoretzkyFiniteDimensionalSectionFromEventFlow

instance dvoretzkyFiniteDimensionalSectionChapterTasteGate :
    ChapterTasteGate DvoretzkyFiniteDimensionalSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dvoretzkyFiniteDimensionalSectionFromEventFlow
          (dvoretzkyFiniteDimensionalSectionToEventFlow x) =
        some x
    exact DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_injective heq)

instance dvoretzkyFiniteDimensionalSectionFieldFaithful :
    FieldFaithful DvoretzkyFiniteDimensionalSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dvoretzkyFiniteDimensionalSectionFields
  field_faithful := DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_fields

instance dvoretzkyFiniteDimensionalSectionNontrivial :
    Nontrivial DvoretzkyFiniteDimensionalSectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DvoretzkyFiniteDimensionalSectionUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DvoretzkyFiniteDimensionalSectionUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DvoretzkyFiniteDimensionalSectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dvoretzkyFiniteDimensionalSectionChapterTasteGate

theorem DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dvoretzkyFiniteDimensionalSectionDecodeBHist
          (dvoretzkyFiniteDimensionalSectionEncodeBHist h) =
        h) ∧
      (∀ x : DvoretzkyFiniteDimensionalSectionUp,
        dvoretzkyFiniteDimensionalSectionFromEventFlow
            (dvoretzkyFiniteDimensionalSectionToEventFlow x) =
          some x) ∧
        (∀ x y : DvoretzkyFiniteDimensionalSectionUp,
          dvoretzkyFiniteDimensionalSectionToEventFlow x =
              dvoretzkyFiniteDimensionalSectionToEventFlow y →
            x = y) ∧
          dvoretzkyFiniteDimensionalSectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_decode,
      DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        DvoretzkyFiniteDimensionalSectionTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.DvoretzkyFiniteDimensionalSectionUp
