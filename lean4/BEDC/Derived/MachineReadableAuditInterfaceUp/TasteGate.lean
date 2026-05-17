import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MachineReadableAuditInterfaceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MachineReadableAuditInterfaceUp : Type where
  | mk (S C E R F H K P N : BHist) : MachineReadableAuditInterfaceUp
  deriving DecidableEq

namespace TasteGate

private def MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h =>
      BMark.b0 ::
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h =>
      BMark.b1 ::
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist h

private def MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, head :: _ => head
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest =>
      MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt n rest

private def MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow :
    MachineReadableAuditInterfaceUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MachineReadableAuditInterfaceUp.mk S C E R F H K P N =>
      [MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist S,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist C,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist E,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist R,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist F,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist H,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist K,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist P,
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist N]

private def MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option MachineReadableAuditInterfaceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (MachineReadableAuditInterfaceUp.mk
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 0 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 1 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 2 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 3 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 4 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 5 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 6 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 7 ef))
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_rawAt 8 ef)))

private def MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fields :
    MachineReadableAuditInterfaceUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | MachineReadableAuditInterfaceUp.mk S C E R F H K P N => [S, C, E, R, F, H, K, P, N]

private theorem MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : MachineReadableAuditInterfaceUp,
      MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fromEventFlow
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S C E R F H K P N =>
      exact
        congrArg some
          (by
            change
              MachineReadableAuditInterfaceUp.mk
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      S))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      C))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      E))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      R))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      F))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      H))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      K))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      P))
                  (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decodeBHist
                    (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_encodeBHist
                      N)) =
                MachineReadableAuditInterfaceUp.mk S C E R F H K P N
            rw [MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode S,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode C,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode E,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode R,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode F,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode H,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode K,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode P,
              MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_decode N])

private theorem MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_injective
    {x y : MachineReadableAuditInterfaceUp} :
    MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow x =
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fromEventFlow
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow x) =
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fromEventFlow
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_round_trip y)))

private theorem MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : MachineReadableAuditInterfaceUp,
      MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fields x =
        MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 C1 E1 R1 F1 H1 K1 P1 N1 =>
      cases y with
      | mk S2 C2 E2 R2 F2 H2 K2 P2 N2 =>
          cases hfields
          rfl

instance MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_bhistCarrier :
    BHistCarrier MachineReadableAuditInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fromEventFlow

instance MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_chapterTasteGate :
    ChapterTasteGate MachineReadableAuditInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fromEventFlow
          (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_injective heq)

instance MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fieldFaithful :
    FieldFaithful MachineReadableAuditInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fields
  field_faithful :=
    MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_fields_faithful

instance MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_nontrivial :
    BEDC.Meta.TasteGate.Nontrivial MachineReadableAuditInterfaceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MachineReadableAuditInterfaceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MachineReadableAuditInterfaceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem MachineReadableAuditInterfaceTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate MachineReadableAuditInterfaceUp) ∧
      (∀ (x : MachineReadableAuditInterfaceUp),
        ∃ (e : EventFlow), BHistCarrier.fromEventFlow e = some x) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · exact
      ⟨MachineReadableAuditInterfaceTasteGate_single_carrier_alignment_chapterTasteGate⟩
  · intro x
    exact
      ⟨BHistCarrier.toEventFlow x,
        ChapterTasteGate.round_trip x⟩

end TasteGate

end BEDC.Derived.MachineReadableAuditInterfaceUp
