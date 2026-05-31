import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EulerMaclaurinUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EulerMaclaurinUp : Type where
  | mk (S A L U D B Q R Z H C P N : BHist) : EulerMaclaurinUp
  deriving DecidableEq

def eulerMaclaurinEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: eulerMaclaurinEncodeBHist h
  | BHist.e1 h => BMark.b1 :: eulerMaclaurinEncodeBHist h

def eulerMaclaurinDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (eulerMaclaurinDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (eulerMaclaurinDecodeBHist tail)

private theorem EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def eulerMaclaurinFields : EulerMaclaurinUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EulerMaclaurinUp.mk S A L U D B Q R Z H C P N => [S, A, L, U, D, B, Q, R, Z, H, C, P, N]

def eulerMaclaurinToEventFlow : EulerMaclaurinUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (eulerMaclaurinFields x).map eulerMaclaurinEncodeBHist

private def eulerMaclaurinEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => eulerMaclaurinEventAtDefault index rest

def eulerMaclaurinFromEventFlow : EventFlow → Option EulerMaclaurinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (EulerMaclaurinUp.mk
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 0 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 1 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 2 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 3 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 4 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 5 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 6 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 7 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 8 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 9 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 10 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 11 ef))
        (eulerMaclaurinDecodeBHist (eulerMaclaurinEventAtDefault 12 ef)))

private theorem EulerMaclaurinTasteGate_single_carrier_alignment_round_trip :
    ∀ x : EulerMaclaurinUp,
      eulerMaclaurinFromEventFlow (eulerMaclaurinToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S A L U D B Q R Z H C P N =>
      change
        some
          (EulerMaclaurinUp.mk
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist S))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist A))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist L))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist U))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist D))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist B))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist Q))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist R))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist Z))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist H))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist C))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist P))
            (eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist N))) =
          some (EulerMaclaurinUp.mk S A L U D B Q R Z H C P N)
      rw [EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode S,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode A,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode L,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode U,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode D,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode B,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode Q,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode R,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode Z,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode H,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode C,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode P,
        EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode N]

private theorem EulerMaclaurinTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : EulerMaclaurinUp} :
    eulerMaclaurinToEventFlow x = eulerMaclaurinToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      eulerMaclaurinFromEventFlow (eulerMaclaurinToEventFlow x) =
        eulerMaclaurinFromEventFlow (eulerMaclaurinToEventFlow y) :=
    congrArg eulerMaclaurinFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (EulerMaclaurinTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (EulerMaclaurinTasteGate_single_carrier_alignment_round_trip y)))

private theorem EulerMaclaurinTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : EulerMaclaurinUp, eulerMaclaurinFields x = eulerMaclaurinFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S₁ A₁ L₁ U₁ D₁ B₁ Q₁ R₁ Z₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk S₂ A₂ L₂ U₂ D₂ B₂ Q₂ R₂ Z₂ H₂ C₂ P₂ N₂ =>
          injection hfields with hS tail0
          injection tail0 with hA tail1
          injection tail1 with hL tail2
          injection tail2 with hU tail3
          injection tail3 with hD tail4
          injection tail4 with hB tail5
          injection tail5 with hQ tail6
          injection tail6 with hR tail7
          injection tail7 with hZ tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hP tail11
          injection tail11 with hN _
          subst hS
          subst hA
          subst hL
          subst hU
          subst hD
          subst hB
          subst hQ
          subst hR
          subst hZ
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance eulerMaclaurinBHistCarrier : BHistCarrier EulerMaclaurinUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := eulerMaclaurinToEventFlow
  fromEventFlow := eulerMaclaurinFromEventFlow

instance eulerMaclaurinChapterTasteGate : ChapterTasteGate EulerMaclaurinUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change eulerMaclaurinFromEventFlow (eulerMaclaurinToEventFlow x) = some x
    exact EulerMaclaurinTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (EulerMaclaurinTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance eulerMaclaurinFieldFaithful : FieldFaithful EulerMaclaurinUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := eulerMaclaurinFields
  field_faithful := EulerMaclaurinTasteGate_single_carrier_alignment_fields_faithful

instance eulerMaclaurinNontrivial : Nontrivial EulerMaclaurinUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨EulerMaclaurinUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      EulerMaclaurinUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate EulerMaclaurinUp :=
  -- BEDC touchpoint anchor: BHist BMark
  eulerMaclaurinChapterTasteGate

theorem EulerMaclaurinTasteGate_single_carrier_alignment :
    (∀ h : BHist, eulerMaclaurinDecodeBHist (eulerMaclaurinEncodeBHist h) = h) ∧
      (∀ x : EulerMaclaurinUp,
        eulerMaclaurinFromEventFlow (eulerMaclaurinToEventFlow x) = some x) ∧
        (∀ x y : EulerMaclaurinUp,
          eulerMaclaurinToEventFlow x = eulerMaclaurinToEventFlow y → x = y) ∧
          eulerMaclaurinEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨EulerMaclaurinTasteGate_single_carrier_alignment_decode_encode,
      EulerMaclaurinTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        EulerMaclaurinTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.EulerMaclaurinUp
