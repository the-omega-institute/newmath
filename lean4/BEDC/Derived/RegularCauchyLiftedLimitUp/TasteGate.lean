import BEDC.FKernel.Ask
import BEDC.FKernel.Hist
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.Package
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyLiftedLimitUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Hist
open BEDC.FKernel.Cont
open BEDC.FKernel.Mark
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyLiftedLimitUp : Type where
  | mk (D S R W E H C P N : BHist) : RegularCauchyLiftedLimitUp
  deriving DecidableEq

def regularCauchyLiftedLimitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyLiftedLimitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyLiftedLimitEncodeBHist h

def regularCauchyLiftedLimitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyLiftedLimitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyLiftedLimitDecodeBHist tail)

private theorem regularCauchyLiftedLimit_decode_encode :
    ∀ h : BHist,
      regularCauchyLiftedLimitDecodeBHist
        (regularCauchyLiftedLimitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyLiftedLimitFields :
    RegularCauchyLiftedLimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RegularCauchyLiftedLimitUp.mk D S R W E H C P N =>
      [D, S, R, W, E, H, C, P, N]

def regularCauchyLiftedLimitToEventFlow :
    RegularCauchyLiftedLimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (regularCauchyLiftedLimitFields x).map regularCauchyLiftedLimitEncodeBHist

private def regularCauchyLiftedLimitRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyLiftedLimitRawAt index rest

private def regularCauchyLiftedLimitLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ index, _event :: rest => regularCauchyLiftedLimitLengthEq index rest

def regularCauchyLiftedLimitFromEventFlow :
    EventFlow → Option RegularCauchyLiftedLimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match regularCauchyLiftedLimitLengthEq 9 flow with
      | true =>
          some
            (RegularCauchyLiftedLimitUp.mk
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 0 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 1 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 2 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 3 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 4 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 5 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 6 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 7 flow))
              (regularCauchyLiftedLimitDecodeBHist
                (regularCauchyLiftedLimitRawAt 8 flow)))
      | false => none

private theorem regularCauchyLiftedLimit_round_trip :
    ∀ x : RegularCauchyLiftedLimitUp,
      regularCauchyLiftedLimitFromEventFlow
        (regularCauchyLiftedLimitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D S R W E H C P N =>
      change
        some
          (RegularCauchyLiftedLimitUp.mk
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist D))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist S))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist R))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist W))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist E))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist H))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist C))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist P))
            (regularCauchyLiftedLimitDecodeBHist
              (regularCauchyLiftedLimitEncodeBHist N))) =
          some (RegularCauchyLiftedLimitUp.mk D S R W E H C P N)
      rw [regularCauchyLiftedLimit_decode_encode D,
        regularCauchyLiftedLimit_decode_encode S,
        regularCauchyLiftedLimit_decode_encode R,
        regularCauchyLiftedLimit_decode_encode W,
        regularCauchyLiftedLimit_decode_encode E,
        regularCauchyLiftedLimit_decode_encode H,
        regularCauchyLiftedLimit_decode_encode C,
        regularCauchyLiftedLimit_decode_encode P,
        regularCauchyLiftedLimit_decode_encode N]

private theorem regularCauchyLiftedLimitToEventFlow_injective
    {x y : RegularCauchyLiftedLimitUp} :
    regularCauchyLiftedLimitToEventFlow x =
        regularCauchyLiftedLimitToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      regularCauchyLiftedLimitFromEventFlow
          (regularCauchyLiftedLimitToEventFlow x) =
        regularCauchyLiftedLimitFromEventFlow
          (regularCauchyLiftedLimitToEventFlow y) :=
    congrArg regularCauchyLiftedLimitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyLiftedLimit_round_trip x).symm
      (Eq.trans hread (regularCauchyLiftedLimit_round_trip y)))

instance regularCauchyLiftedLimitBHistCarrier :
    BHistCarrier RegularCauchyLiftedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyLiftedLimitToEventFlow
  fromEventFlow := regularCauchyLiftedLimitFromEventFlow

instance regularCauchyLiftedLimitChapterTasteGate :
    ChapterTasteGate RegularCauchyLiftedLimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyLiftedLimitFromEventFlow
        (regularCauchyLiftedLimitToEventFlow x) = some x
    exact regularCauchyLiftedLimit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyLiftedLimitToEventFlow_injective heq)

namespace TasteGate

theorem RegularCauchyLiftedLimitNamecertObligations
    (x : RegularCauchyLiftedLimitUp) :
    ∃ D S R W E H C P N : BHist,
      x = RegularCauchyLiftedLimitUp.mk D S R W E H C P N ∧
        regularCauchyLiftedLimitFields x = [D, S, R, W, E, H, C, P, N] ∧
          List.Mem D (regularCauchyLiftedLimitFields x) ∧
            List.Mem E (regularCauchyLiftedLimitFields x) ∧
              BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow x) = some x ∧
                regularCauchyLiftedLimitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  cases x with
  | mk D S R W E H C P N =>
      exists D, S, R, W, E, H, C, P, N
      exact
        ⟨rfl, rfl, List.Mem.head _,
          List.Mem.tail _
            (List.Mem.tail _
              (List.Mem.tail _
                (List.Mem.tail _ (List.Mem.head _)))),
          regularCauchyLiftedLimit_round_trip
            (RegularCauchyLiftedLimitUp.mk D S R W E H C P N),
          rfl⟩

end TasteGate

theorem RegularCauchyLiftedLimitCarrier_namecert_obligations
    [AskSetup] [PackageSetup] (x : RegularCauchyLiftedLimitUp) :
    (∀ h : BHist, Cont h BHist.Empty h) ∧
      (Pkg = Pkg) ∧
        ∃ D S R W E H C P N : BHist,
          x = RegularCauchyLiftedLimitUp.mk D S R W E H C P N ∧
            regularCauchyLiftedLimitFromEventFlow
                (regularCauchyLiftedLimitToEventFlow x) =
              some x := by
  -- BEDC touchpoint anchor: BHist Cont Pkg
  constructor
  · intro h
    exact cont_intro rfl
  · constructor
    · rfl
    · cases x with
      | mk D S R W E H C P N =>
          exact
            ⟨D, S, R, W, E, H, C, P, N, rfl,
              regularCauchyLiftedLimit_round_trip
                (RegularCauchyLiftedLimitUp.mk D S R W E H C P N)⟩

end BEDC.Derived.RegularCauchyLiftedLimitUp
