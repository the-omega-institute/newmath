import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ChebyshevEquioscillationUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ChebyshevEquioscillationUp : Type where
  | mk (I F nu P S Sigma A R H C Q N : BHist) : ChebyshevEquioscillationUp
  deriving DecidableEq

def chebyshevEquioscillationEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: chebyshevEquioscillationEncodeBHist h
  | BHist.e1 h => BMark.b1 :: chebyshevEquioscillationEncodeBHist h

def chebyshevEquioscillationDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (chebyshevEquioscillationDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (chebyshevEquioscillationDecodeBHist tail)

private theorem ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def chebyshevEquioscillationFields : ChebyshevEquioscillationUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ChebyshevEquioscillationUp.mk I F nu P S Sigma A R H C Q N =>
      [I, F, nu, P, S, Sigma, A, R, H, C, Q, N]

def chebyshevEquioscillationToEventFlow : ChebyshevEquioscillationUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map chebyshevEquioscillationEncodeBHist (chebyshevEquioscillationFields x)

private def chebyshevEquioscillationRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => chebyshevEquioscillationRawAt index rest

def chebyshevEquioscillationFromEventFlow
    (flow : EventFlow) : Option ChebyshevEquioscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ChebyshevEquioscillationUp.mk
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 0 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 1 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 2 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 3 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 4 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 5 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 6 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 7 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 8 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 9 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 10 flow))
      (chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationRawAt 11 flow)))

private theorem ChebyshevEquioscillationTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ChebyshevEquioscillationUp,
      chebyshevEquioscillationFromEventFlow
          (chebyshevEquioscillationToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I F nu P S Sigma A R H C Q N =>
      change
        some
          (ChebyshevEquioscillationUp.mk
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist I))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist F))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist nu))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist P))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist S))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist Sigma))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist A))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist R))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist H))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist C))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist Q))
            (chebyshevEquioscillationDecodeBHist
              (chebyshevEquioscillationEncodeBHist N))) =
          some (ChebyshevEquioscillationUp.mk I F nu P S Sigma A R H C Q N)
      rw [ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode I,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode F,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode nu,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode P,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode S,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode Sigma,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode A,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode R,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode H,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode C,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode Q,
        ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode N]

private theorem chebyshevEquioscillationToEventFlow_injective
    {x y : ChebyshevEquioscillationUp} :
    chebyshevEquioscillationToEventFlow x = chebyshevEquioscillationToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      chebyshevEquioscillationFromEventFlow (chebyshevEquioscillationToEventFlow x) =
        chebyshevEquioscillationFromEventFlow (chebyshevEquioscillationToEventFlow y) :=
    congrArg chebyshevEquioscillationFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (ChebyshevEquioscillationTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ChebyshevEquioscillationTasteGate_single_carrier_alignment_round_trip y)))

instance chebyshevEquioscillationBHistCarrier :
    BHistCarrier ChebyshevEquioscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := chebyshevEquioscillationToEventFlow
  fromEventFlow := chebyshevEquioscillationFromEventFlow

instance chebyshevEquioscillationChapterTasteGate :
    ChapterTasteGate ChebyshevEquioscillationUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      chebyshevEquioscillationFromEventFlow (chebyshevEquioscillationToEventFlow x) =
        some x
    exact ChebyshevEquioscillationTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (chebyshevEquioscillationToEventFlow_injective heq)

def taste_gate : ChapterTasteGate ChebyshevEquioscillationUp :=
  -- BEDC touchpoint anchor: BHist BMark
  chebyshevEquioscillationChapterTasteGate

theorem ChebyshevEquioscillationTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      chebyshevEquioscillationDecodeBHist (chebyshevEquioscillationEncodeBHist h) = h) ∧
      (∀ x : ChebyshevEquioscillationUp,
        chebyshevEquioscillationFromEventFlow
            (chebyshevEquioscillationToEventFlow x) =
          some x) ∧
        (∀ x y : ChebyshevEquioscillationUp,
          chebyshevEquioscillationToEventFlow x =
            chebyshevEquioscillationToEventFlow y →
          x = y) ∧
          chebyshevEquioscillationEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨ChebyshevEquioscillationTasteGate_single_carrier_alignment_decode,
      ChebyshevEquioscillationTasteGate_single_carrier_alignment_round_trip,
      by
        intro x y heq
        exact chebyshevEquioscillationToEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.ChebyshevEquioscillationUp
