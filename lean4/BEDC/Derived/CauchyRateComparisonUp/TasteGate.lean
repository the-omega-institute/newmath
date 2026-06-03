import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary.History
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRateComparisonUp : Type where
  | mk (R0 R1 W D Q E H C P N : BHist) : CauchyRateComparisonUp
  deriving DecidableEq

def cauchyRateComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateComparisonEncodeBHist h

def cauchyRateComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateComparisonDecodeBHist tail)

private theorem CauchyRateComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRateComparisonFields : CauchyRateComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateComparisonUp.mk R0 R1 W D Q E H C P N => [R0, R1, W, D, Q, E, H, C, P, N]

def cauchyRateComparisonToEventFlow : CauchyRateComparisonUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateComparisonUp.mk R0 R1 W D Q E H C P N =>
      [[BMark.b0],
        cauchyRateComparisonEncodeBHist R0,
        [BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist R1,
        [BMark.b1, BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist W,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist D,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist Q,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist E,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist H,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cauchyRateComparisonEncodeBHist C,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist P,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cauchyRateComparisonEncodeBHist N]

private def cauchyRateComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRateComparisonEventAtDefault index rest

def cauchyRateComparisonFromEventFlow (ef : EventFlow) : Option CauchyRateComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRateComparisonUp.mk
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 1 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 3 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 5 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 7 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 9 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 11 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 13 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 15 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 17 ef))
      (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEventAtDefault 19 ef)))

private theorem CauchyRateComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRateComparisonUp,
      cauchyRateComparisonFromEventFlow (cauchyRateComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R0 R1 W D Q E H C P N =>
      change
        some
          (CauchyRateComparisonUp.mk
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist R0))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist R1))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist W))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist D))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist Q))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist E))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist H))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist C))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist P))
            (cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist N))) =
          some (CauchyRateComparisonUp.mk R0 R1 W D Q E H C P N)
      rw [CauchyRateComparisonTasteGate_single_carrier_alignment_decode R0,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode R1,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode W,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode D,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode Q,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode E,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode H,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode C,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode P,
        CauchyRateComparisonTasteGate_single_carrier_alignment_decode N]

private theorem cauchyRateComparisonToEventFlow_injective
    {x y : CauchyRateComparisonUp} :
    cauchyRateComparisonToEventFlow x = cauchyRateComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateComparisonFromEventFlow (cauchyRateComparisonToEventFlow x) =
        cauchyRateComparisonFromEventFlow (cauchyRateComparisonToEventFlow y) :=
    congrArg cauchyRateComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyRateComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRateComparisonTasteGate_single_carrier_alignment_round_trip y)))

private theorem cauchyRateComparison_field_faithful :
    ∀ x y : CauchyRateComparisonUp,
      cauchyRateComparisonFields x = cauchyRateComparisonFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk R0 R1 W D Q E H C P N =>
      cases y with
      | mk R0' R1' W' D' Q' E' H' C' P' N' =>
          cases hfields
          rfl

instance cauchyRateComparisonBHistCarrier : BHistCarrier CauchyRateComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateComparisonToEventFlow
  fromEventFlow := cauchyRateComparisonFromEventFlow

instance cauchyRateComparisonChapterTasteGate :
    ChapterTasteGate CauchyRateComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateComparisonFromEventFlow (cauchyRateComparisonToEventFlow x) = some x
    exact CauchyRateComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cauchyRateComparisonToEventFlow_injective heq)

instance cauchyRateComparisonFieldFaithful : FieldFaithful CauchyRateComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cauchyRateComparisonFields
  field_faithful := cauchyRateComparison_field_faithful

instance cauchyRateComparisonNontrivial :
    BEDC.Meta.TasteGate.Nontrivial CauchyRateComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CauchyRateComparisonUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CauchyRateComparisonUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate CauchyRateComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRateComparisonChapterTasteGate

theorem CauchyRateComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyRateComparisonDecodeBHist (cauchyRateComparisonEncodeBHist h) = h) ∧
      (∀ x : CauchyRateComparisonUp,
        cauchyRateComparisonFromEventFlow (cauchyRateComparisonToEventFlow x) = some x) ∧
      (∀ x y : CauchyRateComparisonUp,
        cauchyRateComparisonToEventFlow x = cauchyRateComparisonToEventFlow y → x = y) ∧
      cauchyRateComparisonEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CauchyRateComparisonTasteGate_single_carrier_alignment_decode
  constructor
  · exact CauchyRateComparisonTasteGate_single_carrier_alignment_round_trip
  constructor
  · intro x y heq
    exact cauchyRateComparisonToEventFlow_injective heq
  · rfl

theorem CauchyRateComparisonCommonRefinement
    {R0 R1 W D Q E H C P N leftRead rightRead dyadicRead readbackRead sealRead : BHist} :
    UnaryHistory R0 → UnaryHistory R1 → UnaryHistory W → UnaryHistory D →
      UnaryHistory Q → UnaryHistory E → Cont R0 W leftRead → Cont R1 W rightRead →
        Cont W D dyadicRead → Cont dyadicRead Q readbackRead →
          Cont readbackRead E sealRead →
            cauchyRateComparisonFields
                (CauchyRateComparisonUp.mk R0 R1 W D Q E H C P N) =
              [R0, R1, W, D, Q, E, H, C, P, N] ∧
              UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                UnaryHistory dyadicRead ∧ UnaryHistory readbackRead ∧
                  UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory
  intro unaryR0 unaryR1 unaryW unaryD unaryQ unaryE
  intro leftRoute rightRoute dyadicRoute readbackRoute sealRoute
  have leftUnary : UnaryHistory leftRead :=
    unary_cont_closed unaryR0 unaryW leftRoute
  have rightUnary : UnaryHistory rightRead :=
    unary_cont_closed unaryR1 unaryW rightRoute
  have dyadicUnary : UnaryHistory dyadicRead :=
    unary_cont_closed unaryW unaryD dyadicRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed dyadicUnary unaryQ readbackRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed readbackUnary unaryE sealRoute
  exact ⟨rfl, leftUnary, rightUnary, dyadicUnary, readbackUnary, sealUnary⟩

end BEDC.Derived.CauchyRateComparisonUp
