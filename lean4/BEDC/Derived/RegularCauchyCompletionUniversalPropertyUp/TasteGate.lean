import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionUniversalPropertyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionUniversalPropertyUp : Type where
  | mk (D W Q R M F S E L H C P N : BHist) :
      RegularCauchyCompletionUniversalPropertyUp
  deriving DecidableEq

def regularCauchyCompletionUniversalPropertyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionUniversalPropertyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionUniversalPropertyEncodeBHist h

def regularCauchyCompletionUniversalPropertyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionUniversalPropertyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionUniversalPropertyDecodeBHist tail)

private theorem RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionUniversalPropertyFields :
    RegularCauchyCompletionUniversalPropertyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyCompletionUniversalPropertyUp.mk D W Q R M F S E L H C P N =>
      [D, W, Q, R, M, F, S, E, L, H, C, P, N]

def regularCauchyCompletionUniversalPropertyToEventFlow :
    RegularCauchyCompletionUniversalPropertyUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (regularCauchyCompletionUniversalPropertyFields x).map
      regularCauchyCompletionUniversalPropertyEncodeBHist

private def regularCauchyCompletionUniversalPropertyEventAtDefault :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      regularCauchyCompletionUniversalPropertyEventAtDefault index rest

def regularCauchyCompletionUniversalPropertyFromEventFlow :
    EventFlow → Option RegularCauchyCompletionUniversalPropertyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyCompletionUniversalPropertyUp.mk
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 0 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 1 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 2 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 3 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 4 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 5 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 6 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 7 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 8 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 9 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 10 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 11 ef))
        (regularCauchyCompletionUniversalPropertyDecodeBHist
          (regularCauchyCompletionUniversalPropertyEventAtDefault 12 ef)))

private theorem RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RegularCauchyCompletionUniversalPropertyUp,
      regularCauchyCompletionUniversalPropertyFromEventFlow
          (regularCauchyCompletionUniversalPropertyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W Q R M F S E L H C P N =>
      change
        some
            (RegularCauchyCompletionUniversalPropertyUp.mk
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist D))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist W))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist Q))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist R))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist M))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist F))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist S))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist E))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist L))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist H))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist C))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist P))
              (regularCauchyCompletionUniversalPropertyDecodeBHist
                (regularCauchyCompletionUniversalPropertyEncodeBHist N))) =
          some (RegularCauchyCompletionUniversalPropertyUp.mk D W Q R M F S E L H C P N)
      rw [RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode D,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode W,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode Q,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode R,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode M,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode F,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode S,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode E,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode L,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode H,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode C,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode P,
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode N]

private theorem RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : RegularCauchyCompletionUniversalPropertyUp} :
    regularCauchyCompletionUniversalPropertyToEventFlow x =
        regularCauchyCompletionUniversalPropertyToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyCompletionUniversalPropertyFromEventFlow
          (regularCauchyCompletionUniversalPropertyToEventFlow x) =
        regularCauchyCompletionUniversalPropertyFromEventFlow
          (regularCauchyCompletionUniversalPropertyToEventFlow y) :=
    congrArg regularCauchyCompletionUniversalPropertyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip
        x).symm
      (Eq.trans hread
        (RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip y)))

instance regularCauchyCompletionUniversalPropertyBHistCarrier :
    BHistCarrier RegularCauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionUniversalPropertyToEventFlow
  fromEventFlow := regularCauchyCompletionUniversalPropertyFromEventFlow

instance regularCauchyCompletionUniversalPropertyChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionUniversalPropertyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionUniversalPropertyFromEventFlow
          (regularCauchyCompletionUniversalPropertyToEventFlow x) =
        some x
    exact RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

theorem RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        regularCauchyCompletionUniversalPropertyDecodeBHist
            (regularCauchyCompletionUniversalPropertyEncodeBHist h) =
          h) ∧
      (∀ x : RegularCauchyCompletionUniversalPropertyUp,
        regularCauchyCompletionUniversalPropertyFromEventFlow
            (regularCauchyCompletionUniversalPropertyToEventFlow x) =
          some x) ∧
        (∀ x y : RegularCauchyCompletionUniversalPropertyUp,
          regularCauchyCompletionUniversalPropertyToEventFlow x =
              regularCauchyCompletionUniversalPropertyToEventFlow y →
            x = y) ∧
          regularCauchyCompletionUniversalPropertyEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_decode,
      RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        RegularCauchyCompletionUniversalPropertyTasteGate_single_carrier_alignment_toEventFlow_injective
          heq),
      rfl⟩

end BEDC.Derived.RegularCauchyCompletionUniversalPropertyUp
