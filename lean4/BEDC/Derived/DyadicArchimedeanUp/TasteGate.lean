import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicArchimedeanUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicArchimedeanUp : Type where
  | mk (D B K S C I H T P N : BHist) : DyadicArchimedeanUp
  deriving DecidableEq

def dyadicArchimedeanEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicArchimedeanEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicArchimedeanEncodeBHist h

def dyadicArchimedeanDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicArchimedeanDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicArchimedeanDecodeBHist tail)

theorem DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist, dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def dyadicArchimedeanFields : DyadicArchimedeanUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicArchimedeanUp.mk D B K S C I H T P N => [D, B, K, S, C, I, H, T, P, N]

def dyadicArchimedeanToEventFlow : DyadicArchimedeanUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (dyadicArchimedeanFields x).map dyadicArchimedeanEncodeBHist

private def dyadicArchimedeanRawAt : Nat -> EventFlow -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => dyadicArchimedeanRawAt n rest

private def dyadicArchimedeanLengthEq : Nat -> EventFlow -> Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => dyadicArchimedeanLengthEq n rest

def dyadicArchimedeanFromEventFlow : EventFlow -> Option DyadicArchimedeanUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match dyadicArchimedeanLengthEq 10 flow with
      | true =>
          some
            (DyadicArchimedeanUp.mk
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 0 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 1 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 2 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 3 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 4 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 5 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 6 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 7 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 8 flow))
              (dyadicArchimedeanDecodeBHist (dyadicArchimedeanRawAt 9 flow)))
      | false => none

theorem DyadicArchimedeanTasteGate_single_carrier_alignment_round_trip :
    forall x : DyadicArchimedeanUp,
      dyadicArchimedeanFromEventFlow (dyadicArchimedeanToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D B K S C I H T P N =>
      change
        some
          (DyadicArchimedeanUp.mk
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist D))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist B))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist K))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist S))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist C))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist I))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist H))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist T))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist P))
            (dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist N))) =
          some (DyadicArchimedeanUp.mk D B K S C I H T P N)
      rw [DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode D,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode B,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode K,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode S,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode C,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode I,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode H,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode T,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode P,
        DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode N]

theorem DyadicArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : DyadicArchimedeanUp} :
    dyadicArchimedeanToEventFlow x = dyadicArchimedeanToEventFlow y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicArchimedeanFromEventFlow (dyadicArchimedeanToEventFlow x) =
        dyadicArchimedeanFromEventFlow (dyadicArchimedeanToEventFlow y) :=
    congrArg dyadicArchimedeanFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (DyadicArchimedeanTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (DyadicArchimedeanTasteGate_single_carrier_alignment_round_trip y)))

theorem DyadicArchimedeanTasteGate_single_carrier_alignment_field_faithful :
    forall x y : DyadicArchimedeanUp, dyadicArchimedeanFields x = dyadicArchimedeanFields y ->
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk D1 B1 K1 S1 C1 I1 H1 T1 P1 N1 =>
      cases y with
      | mk D2 B2 K2 S2 C2 I2 H2 T2 P2 N2 =>
          cases hfields
          rfl

instance dyadicArchimedeanBHistCarrier : BHistCarrier DyadicArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicArchimedeanToEventFlow
  fromEventFlow := dyadicArchimedeanFromEventFlow

instance dyadicArchimedeanChapterTasteGate : ChapterTasteGate DyadicArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicArchimedeanFromEventFlow (dyadicArchimedeanToEventFlow x) = some x
    exact DyadicArchimedeanTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (DyadicArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance dyadicArchimedeanFieldFaithful : FieldFaithful DyadicArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := dyadicArchimedeanFields
  field_faithful := DyadicArchimedeanTasteGate_single_carrier_alignment_field_faithful

instance dyadicArchimedeanNontrivial : Nontrivial DyadicArchimedeanUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicArchimedeanUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicArchimedeanUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem DyadicArchimedeanTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate DyadicArchimedeanUp) ∧
      Nonempty (FieldFaithful DyadicArchimedeanUp) ∧
        Nonempty (Nontrivial DyadicArchimedeanUp) ∧
          (∀ h : BHist, dyadicArchimedeanDecodeBHist (dyadicArchimedeanEncodeBHist h) = h) ∧
            (∀ x : DyadicArchimedeanUp,
              dyadicArchimedeanFromEventFlow (dyadicArchimedeanToEventFlow x) = some x) ∧
              (∀ x y : DyadicArchimedeanUp,
                dyadicArchimedeanToEventFlow x = dyadicArchimedeanToEventFlow y -> x = y) ∧
                dyadicArchimedeanEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨dyadicArchimedeanChapterTasteGate⟩
  · constructor
    · exact ⟨dyadicArchimedeanFieldFaithful⟩
    · constructor
      · exact ⟨dyadicArchimedeanNontrivial⟩
      · constructor
        · exact DyadicArchimedeanTasteGate_single_carrier_alignment_decode_encode
        · constructor
          · exact DyadicArchimedeanTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact DyadicArchimedeanTasteGate_single_carrier_alignment_toEventFlow_injective heq
            · rfl

end BEDC.Derived.DyadicArchimedeanUp.TasteGate
