import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyCompletionUniversalUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyCompletionUniversalUp : Type where
  | mk (S W D R A E L H C P N : BHist) : RegularCauchyCompletionUniversalUp
  deriving DecidableEq

def regularCauchyCompletionUniversalEncodeBHist : BHist → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyCompletionUniversalEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyCompletionUniversalEncodeBHist h

def regularCauchyCompletionUniversalDecodeBHist : RawEvent → BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyCompletionUniversalDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyCompletionUniversalDecodeBHist tail)

private theorem RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def regularCauchyCompletionUniversalFields :
    RegularCauchyCompletionUniversalUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyCompletionUniversalUp.mk S W D R A E L H C P N =>
      [S, W, D, R, A, E, L, H, C, P, N]

def regularCauchyCompletionUniversalToEventFlow :
    RegularCauchyCompletionUniversalUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | RegularCauchyCompletionUniversalUp.mk S W D R A E L H C P N =>
      [regularCauchyCompletionUniversalEncodeBHist S,
        regularCauchyCompletionUniversalEncodeBHist W,
        regularCauchyCompletionUniversalEncodeBHist D,
        regularCauchyCompletionUniversalEncodeBHist R,
        regularCauchyCompletionUniversalEncodeBHist A,
        regularCauchyCompletionUniversalEncodeBHist E,
        regularCauchyCompletionUniversalEncodeBHist L,
        regularCauchyCompletionUniversalEncodeBHist H,
        regularCauchyCompletionUniversalEncodeBHist C,
        regularCauchyCompletionUniversalEncodeBHist P,
        regularCauchyCompletionUniversalEncodeBHist N]

private def regularCauchyCompletionUniversalEventAt : Nat → EventFlow → RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => regularCauchyCompletionUniversalEventAt index rest

def regularCauchyCompletionUniversalFromEventFlow :
    EventFlow → Option RegularCauchyCompletionUniversalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (RegularCauchyCompletionUniversalUp.mk
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 0 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 1 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 2 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 3 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 4 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 5 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 6 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 7 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 8 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 9 ef))
        (regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEventAt 10 ef)))

private theorem regularCauchyCompletionUniversal_round_trip :
    ∀ x : RegularCauchyCompletionUniversalUp,
      regularCauchyCompletionUniversalFromEventFlow
          (regularCauchyCompletionUniversalToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S W D R A E L H C P N =>
      change
        some
            (RegularCauchyCompletionUniversalUp.mk
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist S))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist W))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist D))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist R))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist A))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist E))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist L))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist H))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist C))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist P))
              (regularCauchyCompletionUniversalDecodeBHist
                (regularCauchyCompletionUniversalEncodeBHist N))) =
          some (RegularCauchyCompletionUniversalUp.mk S W D R A E L H C P N)
      rw [RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode S,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode W,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode D,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode R,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode A,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode E,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode L,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode H,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode C,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode P,
        RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode N]

private theorem regularCauchyCompletionUniversalToEventFlow_injective
    {x y : RegularCauchyCompletionUniversalUp} :
    regularCauchyCompletionUniversalToEventFlow x =
        regularCauchyCompletionUniversalToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have hsome : some x = some y := by
    calc
      some x =
          regularCauchyCompletionUniversalFromEventFlow
            (regularCauchyCompletionUniversalToEventFlow x) :=
        (regularCauchyCompletionUniversal_round_trip x).symm
      _ =
          regularCauchyCompletionUniversalFromEventFlow
            (regularCauchyCompletionUniversalToEventFlow y) :=
        congrArg regularCauchyCompletionUniversalFromEventFlow hxy
      _ = some y := regularCauchyCompletionUniversal_round_trip y
  exact Option.some.inj hsome

private theorem regularCauchyCompletionUniversal_field_faithful :
    ∀ x y : RegularCauchyCompletionUniversalUp,
      regularCauchyCompletionUniversalFields x =
          regularCauchyCompletionUniversalFields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk S1 W1 D1 R1 A1 E1 L1 H1 C1 P1 N1 =>
      cases y with
      | mk S2 W2 D2 R2 A2 E2 L2 H2 C2 P2 N2 =>
          injection hfields with hS tail0
          injection tail0 with hW tail1
          injection tail1 with hD tail2
          injection tail2 with hR tail3
          injection tail3 with hA tail4
          injection tail4 with hE tail5
          injection tail5 with hL tail6
          injection tail6 with hH tail7
          injection tail7 with hC tail8
          injection tail8 with hP tail9
          injection tail9 with hN _
          subst hS
          subst hW
          subst hD
          subst hR
          subst hA
          subst hE
          subst hL
          subst hH
          subst hC
          subst hP
          subst hN
          rfl

instance regularCauchyCompletionUniversalBHistCarrier :
    BHistCarrier RegularCauchyCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := regularCauchyCompletionUniversalToEventFlow
  fromEventFlow := regularCauchyCompletionUniversalFromEventFlow

instance regularCauchyCompletionUniversalChapterTasteGate :
    ChapterTasteGate RegularCauchyCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      regularCauchyCompletionUniversalFromEventFlow
          (regularCauchyCompletionUniversalToEventFlow x) =
        some x
    exact regularCauchyCompletionUniversal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyCompletionUniversalToEventFlow_injective heq)

instance regularCauchyCompletionUniversalFieldFaithful :
    FieldFaithful RegularCauchyCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := regularCauchyCompletionUniversalFields
  field_faithful := regularCauchyCompletionUniversal_field_faithful

instance regularCauchyCompletionUniversalNontrivial :
    Nontrivial RegularCauchyCompletionUniversalUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RegularCauchyCompletionUniversalUp.mk BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      RegularCauchyCompletionUniversalUp.mk (BHist.e0 BHist.Empty) BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyCompletionUniversalUp :=
  -- BEDC touchpoint anchor: BHist BMark
  regularCauchyCompletionUniversalChapterTasteGate

theorem RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      regularCauchyCompletionUniversalDecodeBHist
          (regularCauchyCompletionUniversalEncodeBHist h) =
        h) ∧
      (∀ x : RegularCauchyCompletionUniversalUp,
        regularCauchyCompletionUniversalFromEventFlow
            (regularCauchyCompletionUniversalToEventFlow x) =
          some x) ∧
      (∀ x y : RegularCauchyCompletionUniversalUp,
        regularCauchyCompletionUniversalToEventFlow x =
            regularCauchyCompletionUniversalToEventFlow y →
          x = y) ∧
      regularCauchyCompletionUniversalEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨RegularCauchyCompletionUniversalTasteGate_single_carrier_alignment_decode,
      regularCauchyCompletionUniversal_round_trip,
      fun _ _ hxy => regularCauchyCompletionUniversalToEventFlow_injective hxy,
      rfl⟩

theorem RegularCauchyCompletionUniversal_extension_route
    {S W D R A E L H C P N extensionConsumer : BHist} :
    regularCauchyCompletionUniversalFields
          (RegularCauchyCompletionUniversalUp.mk S W D R A E L H C P N) =
        [S, W, D, R, A, E, L, H, C, P, N] →
      UnaryHistory S →
      UnaryHistory W →
      UnaryHistory R →
      UnaryHistory E →
      Cont S W D →
      Cont D R A →
      Cont A E extensionConsumer →
      UnaryHistory D ∧ UnaryHistory A ∧ UnaryHistory extensionConsumer ∧
        Cont S W D ∧ Cont D R A ∧ Cont A E extensionConsumer := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont
  intro _fields sourceUnary windowUnary comparisonUnary extensionUnary sourceWindowRoute
    realSealRoute extensionRoute
  have toleranceUnary : UnaryHistory D :=
    unary_cont_closed sourceUnary windowUnary sourceWindowRoute
  have sealUnary : UnaryHistory A :=
    unary_cont_closed toleranceUnary comparisonUnary realSealRoute
  have consumerUnary : UnaryHistory extensionConsumer :=
    unary_cont_closed sealUnary extensionUnary extensionRoute
  exact
    ⟨toleranceUnary, sealUnary, consumerUnary, sourceWindowRoute, realSealRoute,
      extensionRoute⟩

end BEDC.Derived.RegularCauchyCompletionUniversalUp
