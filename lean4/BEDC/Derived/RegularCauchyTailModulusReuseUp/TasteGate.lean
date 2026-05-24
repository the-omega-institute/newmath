import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyTailModulusReuseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyTailModulusReuseUp : Type where
  | mk (S Q T E L W D M U H C P N : BHist) : RegularCauchyTailModulusReuseUp
  deriving DecidableEq

def regularCauchyTailModulusReuseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyTailModulusReuseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyTailModulusReuseEncodeBHist h

def regularCauchyTailModulusReuseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyTailModulusReuseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyTailModulusReuseDecodeBHist tail)

private theorem RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyTailModulusReuseFields :
    RegularCauchyTailModulusReuseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyTailModulusReuseUp.mk S Q T E L W D M U H C P N =>
      [S, Q, T, E, L, W, D, M, U, H, C, P, N]

def regularCauchyTailModulusReuseToEventFlow :
    RegularCauchyTailModulusReuseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (regularCauchyTailModulusReuseFields x).map
        regularCauchyTailModulusReuseEncodeBHist

private def regularCauchyTailModulusReuseEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyTailModulusReuseEventAt index rest

def regularCauchyTailModulusReuseFromEventFlow (ef : EventFlow) :
    Option RegularCauchyTailModulusReuseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (RegularCauchyTailModulusReuseUp.mk
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 0 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 1 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 2 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 3 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 4 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 5 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 6 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 7 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 8 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 9 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 10 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 11 ef))
      (regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEventAt 12 ef)))

private theorem RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_round_trip
    (x : RegularCauchyTailModulusReuseUp) :
    regularCauchyTailModulusReuseFromEventFlow
      (regularCauchyTailModulusReuseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk S Q T E L W D M U H C P N =>
      change
        some
          (RegularCauchyTailModulusReuseUp.mk
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist S))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist Q))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist T))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist E))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist L))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist W))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist D))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist M))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist U))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist H))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist C))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist P))
            (regularCauchyTailModulusReuseDecodeBHist
              (regularCauchyTailModulusReuseEncodeBHist N))) =
          some (RegularCauchyTailModulusReuseUp.mk S Q T E L W D M U H C P N)
      rw [RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode S,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode Q,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode T,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode E,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode L,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode W,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode D,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode M,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode U,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode H,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode C,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode P,
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode N]

private theorem RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyTailModulusReuseUp} :
    regularCauchyTailModulusReuseToEventFlow x =
        regularCauchyTailModulusReuseToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyTailModulusReuseFromEventFlow
          (regularCauchyTailModulusReuseToEventFlow x) =
        regularCauchyTailModulusReuseFromEventFlow
          (regularCauchyTailModulusReuseToEventFlow y) :=
    congrArg regularCauchyTailModulusReuseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_round_trip y)))

private theorem RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : RegularCauchyTailModulusReuseUp,
      regularCauchyTailModulusReuseFields x =
        regularCauchyTailModulusReuseFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 Q1 T1 E1 L1 W1 D1 M1 U1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 Q2 T2 E2 L2 W2 D2 M2 U2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance regularCauchyTailModulusReuseBHistCarrier :
    BHistCarrier RegularCauchyTailModulusReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyTailModulusReuseToEventFlow
  fromEventFlow := regularCauchyTailModulusReuseFromEventFlow

instance regularCauchyTailModulusReuseChapterTasteGate :
    ChapterTasteGate RegularCauchyTailModulusReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyTailModulusReuseFromEventFlow
        (regularCauchyTailModulusReuseToEventFlow x) = some x
    exact RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance regularCauchyTailModulusReuseFieldFaithful :
    FieldFaithful RegularCauchyTailModulusReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyTailModulusReuseFields
  field_faithful :=
    RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_fields_faithful

instance regularCauchyTailModulusReuseNontrivial :
    Nontrivial RegularCauchyTailModulusReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyTailModulusReuseUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyTailModulusReuseUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate RegularCauchyTailModulusReuseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyTailModulusReuseChapterTasteGate

theorem RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyTailModulusReuseDecodeBHist
        (regularCauchyTailModulusReuseEncodeBHist h) = h) ∧
      (∀ x : RegularCauchyTailModulusReuseUp,
        regularCauchyTailModulusReuseFromEventFlow
          (regularCauchyTailModulusReuseToEventFlow x) = some x) ∧
        (∀ x y : RegularCauchyTailModulusReuseUp,
          regularCauchyTailModulusReuseToEventFlow x =
              regularCauchyTailModulusReuseToEventFlow y →
            x = y) ∧
          regularCauchyTailModulusReuseEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_decode_encode,
      RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyTailModulusReuseTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.RegularCauchyTailModulusReuseUp
