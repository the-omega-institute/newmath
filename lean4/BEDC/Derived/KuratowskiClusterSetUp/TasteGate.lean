import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KuratowskiClusterSetUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KuratowskiClusterSetUp : Type where
  | mk (S F Kh Km C M B X R E T U P N : BHist) : KuratowskiClusterSetUp
  deriving DecidableEq

def kuratowskiClusterSetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kuratowskiClusterSetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kuratowskiClusterSetEncodeBHist h

def kuratowskiClusterSetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kuratowskiClusterSetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kuratowskiClusterSetDecodeBHist tail)

private theorem kuratowskiClusterSet_decode_encode :
    ∀ h : BHist,
      kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def kuratowskiClusterSetFields : KuratowskiClusterSetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N =>
      [S, F, Kh, Km, C, M, B, X, R, E, T, U, P, N]

def kuratowskiClusterSetToEventFlow : KuratowskiClusterSetUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (kuratowskiClusterSetFields x).map kuratowskiClusterSetEncodeBHist

private def kuratowskiClusterSetEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => kuratowskiClusterSetEventAtDefault index rest

def kuratowskiClusterSetFromEventFlow
    (ef : EventFlow) : Option KuratowskiClusterSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (KuratowskiClusterSetUp.mk
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 0 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 1 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 2 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 3 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 4 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 5 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 6 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 7 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 8 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 9 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 10 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 11 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 12 ef))
      (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEventAtDefault 13 ef)))

private theorem kuratowskiClusterSet_round_trip :
    ∀ x : KuratowskiClusterSetUp,
      kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S F Kh Km C M B X R E T U P N =>
      change
        some
          (KuratowskiClusterSetUp.mk
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist S))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist F))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist Kh))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist Km))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist C))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist M))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist B))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist X))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist R))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist E))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist T))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist U))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist P))
            (kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist N))) =
          some (KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N)
      rw [kuratowskiClusterSet_decode_encode S, kuratowskiClusterSet_decode_encode F,
        kuratowskiClusterSet_decode_encode Kh, kuratowskiClusterSet_decode_encode Km,
        kuratowskiClusterSet_decode_encode C, kuratowskiClusterSet_decode_encode M,
        kuratowskiClusterSet_decode_encode B, kuratowskiClusterSet_decode_encode X,
        kuratowskiClusterSet_decode_encode R, kuratowskiClusterSet_decode_encode E,
        kuratowskiClusterSet_decode_encode T, kuratowskiClusterSet_decode_encode U,
        kuratowskiClusterSet_decode_encode P, kuratowskiClusterSet_decode_encode N]

private theorem kuratowskiClusterSetToEventFlow_injective
    {x y : KuratowskiClusterSetUp} :
    kuratowskiClusterSetToEventFlow x = kuratowskiClusterSetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) =
        kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow y) :=
    congrArg kuratowskiClusterSetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kuratowskiClusterSet_round_trip x).symm
      (Eq.trans hread (kuratowskiClusterSet_round_trip y)))

private theorem kuratowskiClusterSet_field_faithful :
    ∀ x y : KuratowskiClusterSetUp,
      kuratowskiClusterSetFields x = kuratowskiClusterSetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S F Kh Km C M B X R E T U P N =>
      cases y with
      | mk S' F' Kh' Km' C' M' B' X' R' E' T' U' P' N' =>
          cases hfields
          rfl

instance kuratowskiClusterSetBHistCarrier :
    BHistCarrier KuratowskiClusterSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kuratowskiClusterSetToEventFlow
  fromEventFlow := kuratowskiClusterSetFromEventFlow

instance kuratowskiClusterSetChapterTasteGate :
    ChapterTasteGate KuratowskiClusterSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) = some x
    exact kuratowskiClusterSet_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kuratowskiClusterSetToEventFlow_injective heq)

instance kuratowskiClusterSetFieldFaithful :
    FieldFaithful KuratowskiClusterSetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := kuratowskiClusterSetFields
  field_faithful := kuratowskiClusterSet_field_faithful

def taste_gate : ChapterTasteGate KuratowskiClusterSetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  kuratowskiClusterSetChapterTasteGate

theorem KuratowskiClusterSetTasteGate_single_carrier_alignment :
    ChapterTasteGate KuratowskiClusterSetUp ∧
      Nonempty (FieldFaithful KuratowskiClusterSetUp) ∧
        (∀ h : BHist,
          kuratowskiClusterSetDecodeBHist (kuratowskiClusterSetEncodeBHist h) = h) ∧
          (∀ x : KuratowskiClusterSetUp,
            kuratowskiClusterSetFromEventFlow (kuratowskiClusterSetToEventFlow x) = some x) ∧
            (∀ x y : KuratowskiClusterSetUp,
              kuratowskiClusterSetToEventFlow x = kuratowskiClusterSetToEventFlow y → x = y) ∧
              kuratowskiClusterSetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact
    ⟨kuratowskiClusterSetChapterTasteGate, ⟨kuratowskiClusterSetFieldFaithful⟩,
      kuratowskiClusterSet_decode_encode, kuratowskiClusterSet_round_trip,
      (fun _ _ heq => kuratowskiClusterSetToEventFlow_injective heq), rfl⟩

end BEDC.Derived.KuratowskiClusterSetUp.TasteGate
