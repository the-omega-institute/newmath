import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalCompactnessUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive NestedIntervalCompactnessUp : Type where
  | mk (I L D W R E H C P N : BHist) : NestedIntervalCompactnessUp
  deriving DecidableEq

def nestedIntervalCompactnessEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalCompactnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalCompactnessEncodeBHist h

def nestedIntervalCompactnessDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalCompactnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalCompactnessDecodeBHist tail)

private theorem nestedIntervalCompactness_decode_encode :
    ∀ h : BHist,
      nestedIntervalCompactnessDecodeBHist
          (nestedIntervalCompactnessEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalCompactnessFields :
    NestedIntervalCompactnessUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | NestedIntervalCompactnessUp.mk I L D W R E H C P N => [I, L, D, W, R, E, H, C, P, N]

def nestedIntervalCompactnessToEventFlow :
    NestedIntervalCompactnessUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | NestedIntervalCompactnessUp.mk I L D W R E H C P N =>
      [nestedIntervalCompactnessEncodeBHist I,
        nestedIntervalCompactnessEncodeBHist L,
        nestedIntervalCompactnessEncodeBHist D,
        nestedIntervalCompactnessEncodeBHist W,
        nestedIntervalCompactnessEncodeBHist R,
        nestedIntervalCompactnessEncodeBHist E,
        nestedIntervalCompactnessEncodeBHist H,
        nestedIntervalCompactnessEncodeBHist C,
        nestedIntervalCompactnessEncodeBHist P,
        nestedIntervalCompactnessEncodeBHist N]

private def nestedIntervalCompactnessEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => nestedIntervalCompactnessEventAt index rest

def nestedIntervalCompactnessFromEventFlow :
    EventFlow → Option NestedIntervalCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (NestedIntervalCompactnessUp.mk
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 0 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 1 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 2 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 3 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 4 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 5 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 6 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 7 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 8 ef))
        (nestedIntervalCompactnessDecodeBHist (nestedIntervalCompactnessEventAt 9 ef)))

private theorem nestedIntervalCompactness_round_trip :
    ∀ x : NestedIntervalCompactnessUp,
      nestedIntervalCompactnessFromEventFlow
          (nestedIntervalCompactnessToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk I L D W R E H C P N =>
      change
        some
          (NestedIntervalCompactnessUp.mk
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist I))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist L))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist D))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist R))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist E))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist H))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist C))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist P))
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist N))) =
          some (NestedIntervalCompactnessUp.mk I L D W R E H C P N)
      rw [nestedIntervalCompactness_decode_encode I,
        nestedIntervalCompactness_decode_encode L,
        nestedIntervalCompactness_decode_encode D,
        nestedIntervalCompactness_decode_encode W,
        nestedIntervalCompactness_decode_encode R,
        nestedIntervalCompactness_decode_encode E,
        nestedIntervalCompactness_decode_encode H,
        nestedIntervalCompactness_decode_encode C,
        nestedIntervalCompactness_decode_encode P,
        nestedIntervalCompactness_decode_encode N]

private theorem NestedIntervalCompactnessToEventFlow_injective
    {x y : NestedIntervalCompactnessUp} :
    nestedIntervalCompactnessToEventFlow x =
        nestedIntervalCompactnessToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          nestedIntervalCompactnessFromEventFlow
            (nestedIntervalCompactnessToEventFlow x) :=
        (nestedIntervalCompactness_round_trip x).symm
      _ =
          nestedIntervalCompactnessFromEventFlow
            (nestedIntervalCompactnessToEventFlow y) :=
        congrArg nestedIntervalCompactnessFromEventFlow hxy
      _ = some y := nestedIntervalCompactness_round_trip y
  exact Option.some.inj hsome

private theorem nestedIntervalCompactness_field_faithful :
    ∀ x y : NestedIntervalCompactnessUp,
      nestedIntervalCompactnessFields x =
          nestedIntervalCompactnessFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk I1 L1 D1 W1 R1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk I2 L2 D2 W2 R2 E2 H2 C2 P2 N2 =>
          injection hfields with hI tail0
          injection tail0 with hL tail1
          injection tail1 with hD tail2
          injection tail2 with hW tail3
          injection tail3 with hR tail4
          injection tail4 with hE tail5
          injection tail5 with hH tail6
          injection tail6 with hC tail7
          injection tail7 with hP tail8
          injection tail8 with hN _
          subst hI
          subst hL
          subst hD
          subst hW
          subst hR
          subst hE
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance nestedIntervalCompactnessBHistCarrier :
    BHistCarrier NestedIntervalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalCompactnessToEventFlow
  fromEventFlow := nestedIntervalCompactnessFromEventFlow

instance nestedIntervalCompactnessChapterTasteGate :
    ChapterTasteGate NestedIntervalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      nestedIntervalCompactnessFromEventFlow
          (nestedIntervalCompactnessToEventFlow x) =
        some x
    exact nestedIntervalCompactness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (NestedIntervalCompactnessToEventFlow_injective heq)

instance nestedIntervalCompactnessFieldFaithful :
    FieldFaithful NestedIntervalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedIntervalCompactnessFields
  field_faithful := nestedIntervalCompactness_field_faithful

instance nestedIntervalCompactnessNontrivial :
    Nontrivial NestedIntervalCompactnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨NestedIntervalCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      NestedIntervalCompactnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate NestedIntervalCompactnessUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalCompactnessChapterTasteGate

theorem NestedIntervalCompactnessTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      nestedIntervalCompactnessDecodeBHist
          (nestedIntervalCompactnessEncodeBHist h) =
        h) ∧
      nestedIntervalCompactnessFields
          (NestedIntervalCompactnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact nestedIntervalCompactness_decode_encode
  · rfl

theorem NestedIntervalCompactnessCarrier_stream_real_route
    (x : NestedIntervalCompactnessUp) :
    ∃ I L D W R E H C P N : BHist,
      x = NestedIntervalCompactnessUp.mk I L D W R E H C P N ∧
        nestedIntervalCompactnessFields x = [I, L, D, W, R, E, H, C, P, N] ∧
          hsame
            (nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W))
            W ∧
            hsame
              (nestedIntervalCompactnessDecodeBHist
                (nestedIntervalCompactnessEncodeBHist R))
              R ∧
              hsame
                (nestedIntervalCompactnessDecodeBHist
                  (nestedIntervalCompactnessEncodeBHist E))
                E ∧
                nestedIntervalCompactnessEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark hsame
  cases x with
  | mk I L D W R E H C P N =>
      refine ⟨I, L, D, W, R, E, H, C, P, N, rfl, rfl, ?_, ?_, ?_, rfl⟩
      · change
          nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist W) =
            W
        exact nestedIntervalCompactness_decode_encode W
      · change
          nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist R) =
            R
        exact nestedIntervalCompactness_decode_encode R
      · change
          nestedIntervalCompactnessDecodeBHist
              (nestedIntervalCompactnessEncodeBHist E) =
            E
        exact nestedIntervalCompactness_decode_encode E

theorem NestedIntervalCompactnessCarrier_real_seal_boundary
    {I L D W R E H C P N prefixRead sealRead : BHist} :
    nestedIntervalCompactnessFields (NestedIntervalCompactnessUp.mk I L D W R E H C P N) =
        [I, L, D, W, R, E, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            Cont W R prefixRead →
              Cont prefixRead E sealRead →
                UnaryHistory prefixRead ∧
                  UnaryHistory sealRead ∧
                    Cont W R prefixRead ∧
                      Cont prefixRead E sealRead ∧
                        hsame
                          (nestedIntervalCompactnessDecodeBHist
                            (nestedIntervalCompactnessEncodeBHist E))
                          E := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fieldRows windowUnary readbackUnary sealUnary prefixRoute sealRoute
  cases fieldRows
  have prefixUnary : UnaryHistory prefixRead :=
    unary_cont_closed windowUnary readbackUnary prefixRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed prefixUnary sealUnary sealRoute
  have sealDecode :
      hsame
        (nestedIntervalCompactnessDecodeBHist
          (nestedIntervalCompactnessEncodeBHist E))
        E := by
    change
      nestedIntervalCompactnessDecodeBHist
          (nestedIntervalCompactnessEncodeBHist E) =
        E
    exact nestedIntervalCompactness_decode_encode E
  exact ⟨prefixUnary, sealReadUnary, prefixRoute, sealRoute, sealDecode⟩

end BEDC.Derived.NestedIntervalCompactnessUp
