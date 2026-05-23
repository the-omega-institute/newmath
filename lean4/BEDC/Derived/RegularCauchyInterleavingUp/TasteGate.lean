import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyInterleavingUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyInterleavingUp : Type where
  | mk (A B SA SB sigma M EA EB E H C P N : BHist) : RegularCauchyInterleavingUp
  deriving DecidableEq

def regularCauchyInterleavingEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyInterleavingEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyInterleavingEncodeBHist h

def regularCauchyInterleavingDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyInterleavingDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyInterleavingDecodeBHist tail)

private theorem regularCauchyInterleaving_decode_encode :
    ∀ h : BHist,
      regularCauchyInterleavingDecodeBHist
          (regularCauchyInterleavingEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyInterleavingFields :
    RegularCauchyInterleavingUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyInterleavingUp.mk A B SA SB sigma M EA EB E H C P N =>
      [A, B, SA, SB, sigma, M, EA, EB, E, H, C, P, N]

def regularCauchyInterleavingToEventFlow :
    RegularCauchyInterleavingUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyInterleavingUp.mk A B SA SB sigma M EA EB E H C P N =>
      [regularCauchyInterleavingEncodeBHist A,
        regularCauchyInterleavingEncodeBHist B,
        regularCauchyInterleavingEncodeBHist SA,
        regularCauchyInterleavingEncodeBHist SB,
        regularCauchyInterleavingEncodeBHist sigma,
        regularCauchyInterleavingEncodeBHist M,
        regularCauchyInterleavingEncodeBHist EA,
        regularCauchyInterleavingEncodeBHist EB,
        regularCauchyInterleavingEncodeBHist E,
        regularCauchyInterleavingEncodeBHist H,
        regularCauchyInterleavingEncodeBHist C,
        regularCauchyInterleavingEncodeBHist P,
        regularCauchyInterleavingEncodeBHist N]

private def regularCauchyInterleavingEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyInterleavingEventAt index rest

def regularCauchyInterleavingFromEventFlow :
    EventFlow → Option RegularCauchyInterleavingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyInterleavingUp.mk
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 0 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 1 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 2 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 3 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 4 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 5 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 6 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 7 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 8 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 9 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 10 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 11 ef))
        (regularCauchyInterleavingDecodeBHist (regularCauchyInterleavingEventAt 12 ef)))

private theorem regularCauchyInterleaving_round_trip :
    ∀ x : RegularCauchyInterleavingUp,
      regularCauchyInterleavingFromEventFlow
          (regularCauchyInterleavingToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk A B SA SB sigma M EA EB E H C P N =>
      change
        some
          (RegularCauchyInterleavingUp.mk
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist A))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist B))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist SA))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist SB))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist sigma))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist M))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist EA))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist EB))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist E))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist H))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist C))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist P))
            (regularCauchyInterleavingDecodeBHist
              (regularCauchyInterleavingEncodeBHist N))) =
          some (RegularCauchyInterleavingUp.mk A B SA SB sigma M EA EB E H C P N)
      rw [regularCauchyInterleaving_decode_encode A,
        regularCauchyInterleaving_decode_encode B,
        regularCauchyInterleaving_decode_encode SA,
        regularCauchyInterleaving_decode_encode SB,
        regularCauchyInterleaving_decode_encode sigma,
        regularCauchyInterleaving_decode_encode M,
        regularCauchyInterleaving_decode_encode EA,
        regularCauchyInterleaving_decode_encode EB,
        regularCauchyInterleaving_decode_encode E,
        regularCauchyInterleaving_decode_encode H,
        regularCauchyInterleaving_decode_encode C,
        regularCauchyInterleaving_decode_encode P,
        regularCauchyInterleaving_decode_encode N]

private theorem regularCauchyInterleavingToEventFlow_injective
    {x y : RegularCauchyInterleavingUp} :
    regularCauchyInterleavingToEventFlow x =
        regularCauchyInterleavingToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          regularCauchyInterleavingFromEventFlow
            (regularCauchyInterleavingToEventFlow x) :=
        (regularCauchyInterleaving_round_trip x).symm
      _ =
          regularCauchyInterleavingFromEventFlow
            (regularCauchyInterleavingToEventFlow y) :=
        congrArg regularCauchyInterleavingFromEventFlow hxy
      _ = some y := regularCauchyInterleaving_round_trip y
  exact Option.some.inj hsome

private theorem regularCauchyInterleaving_field_faithful :
    ∀ x y : RegularCauchyInterleavingUp,
      regularCauchyInterleavingFields x =
          regularCauchyInterleavingFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk A1 B1 SA1 SB1 sigma1 M1 EA1 EB1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk A2 B2 SA2 SB2 sigma2 M2 EA2 EB2 E2 H2 C2 P2 N2 =>
          injection hfields with hA tail0
          injection tail0 with hB tail1
          injection tail1 with hSA tail2
          injection tail2 with hSB tail3
          injection tail3 with hsigma tail4
          injection tail4 with hM tail5
          injection tail5 with hEA tail6
          injection tail6 with hEB tail7
          injection tail7 with hE tail8
          injection tail8 with hH tail9
          injection tail9 with hC tail10
          injection tail10 with hP tail11
          injection tail11 with hN _
          subst hA
          subst hB
          subst hSA
          subst hSB
          subst hsigma
          subst hM
          subst hEA
          subst hEB
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyInterleavingBHistCarrier :
    BHistCarrier RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyInterleavingToEventFlow
  fromEventFlow := regularCauchyInterleavingFromEventFlow

instance regularCauchyInterleavingChapterTasteGate :
    ChapterTasteGate RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyInterleavingFromEventFlow
          (regularCauchyInterleavingToEventFlow x) =
        some x
    exact regularCauchyInterleaving_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyInterleavingToEventFlow_injective heq)

instance regularCauchyInterleavingFieldFaithful :
    FieldFaithful RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyInterleavingFields
  field_faithful := regularCauchyInterleaving_field_faithful

instance regularCauchyInterleavingNontrivial :
    Nontrivial RegularCauchyInterleavingUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyInterleavingUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyInterleavingUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyInterleavingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyInterleavingChapterTasteGate

theorem RegularCauchyInterleavingTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyInterleavingDecodeBHist
          (regularCauchyInterleavingEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyInterleavingUp,
        regularCauchyInterleavingFromEventFlow
            (regularCauchyInterleavingToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyInterleavingUp,
        regularCauchyInterleavingToEventFlow x =
            regularCauchyInterleavingToEventFlow y →
          x = y) ∧
      regularCauchyInterleavingEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨regularCauchyInterleaving_decode_encode,
      regularCauchyInterleaving_round_trip,
      fun _ _ hxy => regularCauchyInterleavingToEventFlow_injective hxy,
      rfl⟩

end BEDC.Derived.RegularCauchyInterleavingUp.TasteGate
