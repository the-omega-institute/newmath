import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.TheoremGapRegistryUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive TheoremGapRegistryUp : Type where
  | mk (T D S G C F A L H P N : BHist) : TheoremGapRegistryUp
  deriving DecidableEq

def theoremGapRegistryEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: theoremGapRegistryEncodeBHist h
  | BHist.e1 h => BMark.b1 :: theoremGapRegistryEncodeBHist h

def theoremGapRegistryDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (theoremGapRegistryDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (theoremGapRegistryDecodeBHist tail)

private theorem theoremGapRegistryDecode_encode_bhist :
    ∀ h : BHist,
      theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private def theoremGapRegistryFields : TheoremGapRegistryUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | TheoremGapRegistryUp.mk T D S G C F A L H P N => [T, D, S, G, C, F, A, L, H, P, N]

def theoremGapRegistryToEventFlow : TheoremGapRegistryUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TheoremGapRegistryUp.mk T D S G C F A L H P N =>
      [[BMark.b0],
        theoremGapRegistryEncodeBHist T,
        [BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist S,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist G,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist F,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist A,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        theoremGapRegistryEncodeBHist L,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        theoremGapRegistryEncodeBHist N]

private def theoremGapRegistryRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => theoremGapRegistryRawAt n rest

private def theoremGapRegistryLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => theoremGapRegistryLengthEq n rest

def theoremGapRegistryFromEventFlow : EventFlow → Option TheoremGapRegistryUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match theoremGapRegistryLengthEq 22 flow with
      | true =>
          some
            (TheoremGapRegistryUp.mk
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 1 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 3 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 5 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 7 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 9 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 11 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 13 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 15 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 17 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 19 flow))
              (theoremGapRegistryDecodeBHist (theoremGapRegistryRawAt 21 flow)))
      | false => none

private theorem theoremGapRegistry_round_trip :
    ∀ x : TheoremGapRegistryUp,
      theoremGapRegistryFromEventFlow (theoremGapRegistryToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk T D S G C F A L H P N =>
      change
        some
          (TheoremGapRegistryUp.mk
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist T))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist D))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist S))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist G))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist C))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist F))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist A))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist L))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist H))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist P))
            (theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist N))) =
          some (TheoremGapRegistryUp.mk T D S G C F A L H P N)
      rw [theoremGapRegistryDecode_encode_bhist T,
        theoremGapRegistryDecode_encode_bhist D,
        theoremGapRegistryDecode_encode_bhist S,
        theoremGapRegistryDecode_encode_bhist G,
        theoremGapRegistryDecode_encode_bhist C,
        theoremGapRegistryDecode_encode_bhist F,
        theoremGapRegistryDecode_encode_bhist A,
        theoremGapRegistryDecode_encode_bhist L,
        theoremGapRegistryDecode_encode_bhist H,
        theoremGapRegistryDecode_encode_bhist P,
        theoremGapRegistryDecode_encode_bhist N]

private theorem theoremGapRegistryToEventFlow_injective
    {x y : TheoremGapRegistryUp} :
    theoremGapRegistryToEventFlow x = theoremGapRegistryToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      theoremGapRegistryFromEventFlow (theoremGapRegistryToEventFlow x) =
        theoremGapRegistryFromEventFlow (theoremGapRegistryToEventFlow y) :=
    congrArg theoremGapRegistryFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (theoremGapRegistry_round_trip x).symm
      (Eq.trans hread (theoremGapRegistry_round_trip y)))

private theorem theoremGapRegistry_field_faithful :
    ∀ x y : TheoremGapRegistryUp,
      theoremGapRegistryFields x = theoremGapRegistryFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk T1 D1 S1 G1 C1 F1 A1 L1 H1 P1 N1 =>
      cases y with
      | mk T2 D2 S2 G2 C2 F2 A2 L2 H2 P2 N2 =>
          cases hfields
          rfl

instance theoremGapRegistryBHistCarrier : BHistCarrier TheoremGapRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := theoremGapRegistryToEventFlow
  fromEventFlow := theoremGapRegistryFromEventFlow

instance theoremGapRegistryChapterTasteGate :
    ChapterTasteGate TheoremGapRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change theoremGapRegistryFromEventFlow (theoremGapRegistryToEventFlow x) = some x
    exact theoremGapRegistry_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (theoremGapRegistryToEventFlow_injective heq)

instance theoremGapRegistryFieldFaithful : FieldFaithful TheoremGapRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := theoremGapRegistryFields
  field_faithful := theoremGapRegistry_field_faithful

instance theoremGapRegistryNontrivial : Nontrivial TheoremGapRegistryUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨TheoremGapRegistryUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      TheoremGapRegistryUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem TheoremGapRegistryTasteGate_single_carrier_alignment :
    theoremGapRegistryEncodeBHist BHist.Empty = ([] : RawEvent) ∧
      theoremGapRegistryEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] ∧
      (∀ h : BHist, theoremGapRegistryDecodeBHist (theoremGapRegistryEncodeBHist h) = h) ∧
      (∀ x : TheoremGapRegistryUp,
        theoremGapRegistryFromEventFlow (theoremGapRegistryToEventFlow x) = some x) ∧
      (∀ x y : TheoremGapRegistryUp,
        theoremGapRegistryToEventFlow x = theoremGapRegistryToEventFlow y → x = y) ∧
      Nonempty (FieldFaithful TheoremGapRegistryUp) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl, rfl, theoremGapRegistryDecode_encode_bhist, theoremGapRegistry_round_trip,
      (fun _ _ heq => theoremGapRegistryToEventFlow_injective heq),
      ⟨theoremGapRegistryFieldFaithful⟩⟩

end BEDC.Derived.TheoremGapRegistryUp
