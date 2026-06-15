import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiClosureComplementUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiClosureComplementUp : Type where
  | mk (T F L C A B H R P N : BHist) : KuratowskiClosureComplementUp
  deriving DecidableEq

def kuratowskiClosureComplementEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiClosureComplementEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiClosureComplementEncodeBHist h

def kuratowskiClosureComplementDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiClosureComplementDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiClosureComplementDecodeBHist tail)

private theorem KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      kuratowskiClosureComplementDecodeBHist
          (kuratowskiClosureComplementEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiClosureComplementFields : KuratowskiClosureComplementUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiClosureComplementUp.mk T F L C A B H R P N => [T, F, L, C, A, B, H, R, P, N]

def kuratowskiClosureComplementToEventFlow : KuratowskiClosureComplementUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (kuratowskiClosureComplementFields x).map kuratowskiClosureComplementEncodeBHist

private def kuratowskiClosureComplementEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kuratowskiClosureComplementEventAt index rest

def kuratowskiClosureComplementFromEventFlow
    (ef : EventFlow) : Option KuratowskiClosureComplementUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KuratowskiClosureComplementUp.mk
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 0 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 1 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 2 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 3 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 4 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 5 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 6 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 7 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 8 ef))
      (kuratowskiClosureComplementDecodeBHist (kuratowskiClosureComplementEventAt 9 ef)))

private theorem KuratowskiClosureComplementTasteGate_single_carrier_alignment_round_trip
    (x : KuratowskiClosureComplementUp) :
    kuratowskiClosureComplementFromEventFlow
        (kuratowskiClosureComplementToEventFlow x) =
      some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk T F L C A B H R P N =>
      change
        some
          (KuratowskiClosureComplementUp.mk
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist T))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist F))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist L))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist C))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist A))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist B))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist H))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist R))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist P))
            (kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist N))) =
          some (KuratowskiClosureComplementUp.mk T F L C A B H R P N)
      rw [KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode T,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode F,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode L,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode C,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode A,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode B,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode H,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode R,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode P,
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode N]

private theorem KuratowskiClosureComplementTasteGate_single_carrier_alignment_injective
    {x y : KuratowskiClosureComplementUp} :
    kuratowskiClosureComplementToEventFlow x =
        kuratowskiClosureComplementToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiClosureComplementFromEventFlow
          (kuratowskiClosureComplementToEventFlow x) =
        kuratowskiClosureComplementFromEventFlow
          (kuratowskiClosureComplementToEventFlow y) :=
    congrArg kuratowskiClosureComplementFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (KuratowskiClosureComplementTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (KuratowskiClosureComplementTasteGate_single_carrier_alignment_round_trip y)))

private theorem KuratowskiClosureComplementTasteGate_single_carrier_alignment_fields :
    ∀ x y : KuratowskiClosureComplementUp,
      kuratowskiClosureComplementFields x = kuratowskiClosureComplementFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 F1 L1 C1 A1 B1 H1 R1 P1 N1 =>
      cases y with
      | mk T2 F2 L2 C2 A2 B2 H2 R2 P2 N2 =>
          cases hfields
          rfl

instance kuratowskiClosureComplementBHistCarrier :
    BHistCarrier KuratowskiClosureComplementUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiClosureComplementToEventFlow
  fromEventFlow := kuratowskiClosureComplementFromEventFlow

instance kuratowskiClosureComplementChapterTasteGate :
    ChapterTasteGate KuratowskiClosureComplementUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kuratowskiClosureComplementFromEventFlow
          (kuratowskiClosureComplementToEventFlow x) =
        some x
    exact KuratowskiClosureComplementTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (KuratowskiClosureComplementTasteGate_single_carrier_alignment_injective heq)

instance kuratowskiClosureComplementFieldFaithful :
    FieldFaithful KuratowskiClosureComplementUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kuratowskiClosureComplementFields
  field_faithful := KuratowskiClosureComplementTasteGate_single_carrier_alignment_fields

instance kuratowskiClosureComplementNontrivial :
    BEDC.Meta.TasteGate.Nontrivial KuratowskiClosureComplementUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KuratowskiClosureComplementUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KuratowskiClosureComplementUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

theorem KuratowskiClosureComplementTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate KuratowskiClosureComplementUp) ∧
      Nonempty (FieldFaithful KuratowskiClosureComplementUp) ∧
        (∀ h : BHist,
          kuratowskiClosureComplementDecodeBHist
              (kuratowskiClosureComplementEncodeBHist h) =
            h) ∧
          (∀ x : KuratowskiClosureComplementUp,
            kuratowskiClosureComplementFromEventFlow
                (kuratowskiClosureComplementToEventFlow x) =
              some x) ∧
            (∀ x y : KuratowskiClosureComplementUp,
              kuratowskiClosureComplementToEventFlow x =
                  kuratowskiClosureComplementToEventFlow y →
                x = y) ∧
              kuratowskiClosureComplementEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨⟨kuratowskiClosureComplementChapterTasteGate⟩,
      ⟨kuratowskiClosureComplementFieldFaithful⟩,
      KuratowskiClosureComplementTasteGate_single_carrier_alignment_decode_encode,
      KuratowskiClosureComplementTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        KuratowskiClosureComplementTasteGate_single_carrier_alignment_injective heq),
      rfl⟩

end BEDC.Derived.KuratowskiClosureComplementUp
