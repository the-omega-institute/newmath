import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyAbsUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyAbsUp : Type where
  | mk (X W D V R E H C P N : BHist) : RegularCauchyAbsUp
  deriving DecidableEq

def regularCauchyAbsEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyAbsEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyAbsEncodeBHist h

def regularCauchyAbsDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyAbsDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyAbsDecodeBHist tail)

private theorem regularCauchyAbs_decode_encode :
    ∀ h : BHist,
      regularCauchyAbsDecodeBHist
          (regularCauchyAbsEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyAbsFields :
    RegularCauchyAbsUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyAbsUp.mk X W D V R E H C P N => [X, W, D, V, R, E, H, C, P, N]

def regularCauchyAbsToEventFlow :
    RegularCauchyAbsUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyAbsUp.mk X W D V R E H C P N =>
      [regularCauchyAbsEncodeBHist X,
        regularCauchyAbsEncodeBHist W,
        regularCauchyAbsEncodeBHist D,
        regularCauchyAbsEncodeBHist V,
        regularCauchyAbsEncodeBHist R,
        regularCauchyAbsEncodeBHist E,
        regularCauchyAbsEncodeBHist H,
        regularCauchyAbsEncodeBHist C,
        regularCauchyAbsEncodeBHist P,
        regularCauchyAbsEncodeBHist N]

private def regularCauchyAbsEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyAbsEventAt index rest

def regularCauchyAbsFromEventFlow :
    EventFlow → Option RegularCauchyAbsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyAbsUp.mk
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 0 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 1 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 2 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 3 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 4 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 5 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 6 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 7 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 8 ef))
        (regularCauchyAbsDecodeBHist (regularCauchyAbsEventAt 9 ef)))

private theorem regularCauchyAbs_round_trip :
    ∀ x : RegularCauchyAbsUp,
      regularCauchyAbsFromEventFlow
          (regularCauchyAbsToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk X W D V R E H C P N =>
      change
        some
          (RegularCauchyAbsUp.mk
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist X))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist W))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist D))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist V))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist R))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist E))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist H))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist C))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist P))
            (regularCauchyAbsDecodeBHist
              (regularCauchyAbsEncodeBHist N))) =
          some (RegularCauchyAbsUp.mk X W D V R E H C P N)
      rw [regularCauchyAbs_decode_encode X,
        regularCauchyAbs_decode_encode W,
        regularCauchyAbs_decode_encode D,
        regularCauchyAbs_decode_encode V,
        regularCauchyAbs_decode_encode R,
        regularCauchyAbs_decode_encode E,
        regularCauchyAbs_decode_encode H,
        regularCauchyAbs_decode_encode C,
        regularCauchyAbs_decode_encode P,
        regularCauchyAbs_decode_encode N]

private theorem RegularCauchyAbsToEventFlow_injective
    {x y : RegularCauchyAbsUp} :
    regularCauchyAbsToEventFlow x =
        regularCauchyAbsToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          regularCauchyAbsFromEventFlow
            (regularCauchyAbsToEventFlow x) :=
        (regularCauchyAbs_round_trip x).symm
      _ =
          regularCauchyAbsFromEventFlow
            (regularCauchyAbsToEventFlow y) :=
        congrArg regularCauchyAbsFromEventFlow hxy
      _ = some y := regularCauchyAbs_round_trip y
  exact Option.some.inj hsome

private theorem regularCauchyAbs_field_faithful :
    ∀ x y : RegularCauchyAbsUp,
      regularCauchyAbsFields x =
          regularCauchyAbsFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk X1 W1 D1 V1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk X2 W2 D2 V2 R2 E2 H2 C2 P2 N2 =>
          injection hfields with hX tail0
          injection tail0 with hW tail1
          injection tail1 with hD tail2
          injection tail2 with hV tail3
          injection tail3 with hR tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hX
          subst hW
          subst hD
          subst hV
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyAbsBHistCarrier :
    BHistCarrier RegularCauchyAbsUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyAbsToEventFlow
  fromEventFlow := regularCauchyAbsFromEventFlow

instance regularCauchyAbsChapterTasteGate :
    ChapterTasteGate RegularCauchyAbsUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyAbsFromEventFlow
          (regularCauchyAbsToEventFlow x) =
        some x
    exact regularCauchyAbs_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RegularCauchyAbsToEventFlow_injective heq)

instance regularCauchyAbsFieldFaithful :
    FieldFaithful RegularCauchyAbsUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyAbsFields
  field_faithful := regularCauchyAbs_field_faithful

instance regularCauchyAbsNontrivial :
    Nontrivial RegularCauchyAbsUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyAbsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RegularCauchyAbsUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyAbsUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyAbsChapterTasteGate

theorem RegularCauchyAbsTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyAbsDecodeBHist
          (regularCauchyAbsEncodeBHist h) =
        h) ∧
      regularCauchyAbsFields
          (RegularCauchyAbsUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact regularCauchyAbs_decode_encode
  · rfl

end BEDC.Derived.RegularCauchyAbsUp
