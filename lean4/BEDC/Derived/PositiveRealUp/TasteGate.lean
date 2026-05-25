import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PositiveRealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Cont
open BEDC.FKernel.NameCert
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PositiveRealUp : Type where
  | mk (R A D W Q H C P N : BHist) : PositiveRealUp
  deriving DecidableEq

def positiveRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: positiveRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: positiveRealEncodeBHist h

def positiveRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (positiveRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (positiveRealDecodeBHist tail)

private theorem positiveReal_decode_encode_bhist :
    ∀ h : BHist, positiveRealDecodeBHist (positiveRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def positiveRealFields : PositiveRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | PositiveRealUp.mk R A D W Q H C P N => [R, A, D, W, Q, H, C, P, N]

def positiveRealToEventFlow : PositiveRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PositiveRealUp.mk R A D W Q H C P N =>
      [positiveRealEncodeBHist R,
        positiveRealEncodeBHist A,
        positiveRealEncodeBHist D,
        positiveRealEncodeBHist W,
        positiveRealEncodeBHist Q,
        positiveRealEncodeBHist H,
        positiveRealEncodeBHist C,
        positiveRealEncodeBHist P,
        positiveRealEncodeBHist N]

private def positiveRealRawAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => []
  | 0, w :: _ => w
  | Nat.succ _, [] => []
  | Nat.succ n, _ :: rest => positiveRealRawAt n rest

private def positiveRealLengthEq : Nat → EventFlow → Bool
  -- BEDC touchpoint anchor: BHist BMark
  | 0, [] => true
  | 0, _ :: _ => false
  | Nat.succ _, [] => false
  | Nat.succ n, _ :: rest => positiveRealLengthEq n rest

def positiveRealFromEventFlow : EventFlow → Option PositiveRealUp
  -- BEDC touchpoint anchor: BHist BMark
  | flow =>
      match positiveRealLengthEq 9 flow with
      | true =>
          some
            (PositiveRealUp.mk
              (positiveRealDecodeBHist (positiveRealRawAt 0 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 1 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 2 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 3 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 4 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 5 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 6 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 7 flow))
              (positiveRealDecodeBHist (positiveRealRawAt 8 flow)))
      | false => none

private theorem positiveReal_round_trip :
    ∀ x : PositiveRealUp,
      positiveRealFromEventFlow (positiveRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk R A D W Q H C P N =>
      change
        some
          (PositiveRealUp.mk
            (positiveRealDecodeBHist (positiveRealEncodeBHist R))
            (positiveRealDecodeBHist (positiveRealEncodeBHist A))
            (positiveRealDecodeBHist (positiveRealEncodeBHist D))
            (positiveRealDecodeBHist (positiveRealEncodeBHist W))
            (positiveRealDecodeBHist (positiveRealEncodeBHist Q))
            (positiveRealDecodeBHist (positiveRealEncodeBHist H))
            (positiveRealDecodeBHist (positiveRealEncodeBHist C))
            (positiveRealDecodeBHist (positiveRealEncodeBHist P))
            (positiveRealDecodeBHist (positiveRealEncodeBHist N))) =
          some (PositiveRealUp.mk R A D W Q H C P N)
      rw [positiveReal_decode_encode_bhist R,
        positiveReal_decode_encode_bhist A,
        positiveReal_decode_encode_bhist D,
        positiveReal_decode_encode_bhist W,
        positiveReal_decode_encode_bhist Q,
        positiveReal_decode_encode_bhist H,
        positiveReal_decode_encode_bhist C,
        positiveReal_decode_encode_bhist P,
        positiveReal_decode_encode_bhist N]

private theorem positiveRealToEventFlow_injective {x y : PositiveRealUp} :
    positiveRealToEventFlow x = positiveRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      positiveRealFromEventFlow (positiveRealToEventFlow x) =
        positiveRealFromEventFlow (positiveRealToEventFlow y) :=
    congrArg positiveRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (positiveReal_round_trip x).symm
      (Eq.trans hread (positiveReal_round_trip y)))

private theorem positiveReal_field_faithful :
    ∀ x y : PositiveRealUp, positiveRealFields x = positiveRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk R1 A1 D1 W1 Q1 H1 C1 P1 N1 =>
      cases y with
      | mk R2 A2 D2 W2 Q2 H2 C2 P2 N2 =>
          cases h
          rfl

instance positiveRealBHistCarrier : BHistCarrier PositiveRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := positiveRealToEventFlow
  fromEventFlow := positiveRealFromEventFlow

instance positiveRealChapterTasteGate : ChapterTasteGate PositiveRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change positiveRealFromEventFlow (positiveRealToEventFlow x) = some x
    exact positiveReal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (positiveRealToEventFlow_injective heq)

instance positiveRealFieldFaithful : FieldFaithful PositiveRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := positiveRealFields
  field_faithful := positiveReal_field_faithful

instance positiveRealNontrivial : Nontrivial PositiveRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PositiveRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PositiveRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate PositiveRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  positiveRealChapterTasteGate

theorem PositiveRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, positiveRealDecodeBHist (positiveRealEncodeBHist h) = h) ∧
      positiveRealFields
          (PositiveRealUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact ⟨positiveReal_decode_encode_bhist, rfl⟩

theorem PositiveRealNameCert_obligations (x : PositiveRealUp) :
    SemanticNameCert
      (fun row : BHist => List.Mem row (positiveRealFields x))
      (fun row : BHist => List.Mem row (positiveRealFields x) ∧ Cont row BHist.Empty row)
      (fun row : BHist =>
        List.Mem row (positiveRealFields x) ∧ hsame (append row BHist.Empty) row)
      hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert
  refine
    { core :=
        { carrier_inhabited := ?carrier_inhabited
          equiv_refl := ?equiv_refl
          equiv_symm := ?equiv_symm
          equiv_trans := ?equiv_trans
          carrier_respects_equiv := ?carrier_respects_equiv }
      pattern_sound := ?pattern_sound
      ledger_sound := ?ledger_sound }
  · cases x with
    | mk R A D W Q H C P N =>
        exact ⟨R, List.Mem.head _⟩
  · intro h _source
    exact hsame_refl h
  · intro h k same
    exact hsame_symm same
  · intro h k r sameHK sameKR
    exact hsame_trans sameHK sameKR
  · intro h k same source
    cases same
    exact source
  · intro h source
    exact ⟨source, cont_right_unit h⟩
  · intro h source
    exact ⟨source, append_empty_right h⟩

def PositiveRealCarrier (R A D W Q H C P N : BHist) : Prop :=
  -- BEDC touchpoint anchor: BHist UnaryHistory
  UnaryHistory R ∧ UnaryHistory A ∧ UnaryHistory D ∧ UnaryHistory W ∧
    UnaryHistory Q ∧ UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧
      UnaryHistory N

theorem PositiveRealCarrier_multiplicative_radius_transport
    {R1 A1 D1 W Q1 H1 C1 P1 N1 R2 A2 D2 Q2 H2 C2 P2 N2 radiusProduct
      transportedRead : BHist} :
    PositiveRealCarrier R1 A1 D1 W Q1 H1 C1 P1 N1 →
      PositiveRealCarrier R2 A2 D2 W Q2 H2 C2 P2 N2 →
        Cont D1 D2 radiusProduct →
          Cont radiusProduct W transportedRead →
            UnaryHistory radiusProduct ∧ UnaryHistory transportedRead ∧
              Cont D1 D2 radiusProduct ∧ Cont radiusProduct W transportedRead ∧
                hsame W W := by
  -- BEDC touchpoint anchor: BHist Cont hsame UnaryHistory
  intro carrierLeft carrierRight radiusRoute transportedRoute
  obtain ⟨_realLeft, _apartLeft, radiusLeft, windowUnary, _readLeft, _handoffLeft,
    _certLeft, _pkgLeft, _nameLeft⟩ := carrierLeft
  obtain ⟨_realRight, _apartRight, radiusRight, _windowRight, _readRight, _handoffRight,
    _certRight, _pkgRight, _nameRight⟩ := carrierRight
  have productUnary : UnaryHistory radiusProduct :=
    unary_cont_closed radiusLeft radiusRight radiusRoute
  have transportedUnary : UnaryHistory transportedRead :=
    unary_cont_closed productUnary windowUnary transportedRoute
  exact
    ⟨productUnary, transportedUnary, radiusRoute, transportedRoute, hsame_refl W⟩

theorem PositiveRealCarrier_apartness_handoff
    {R A D W Q H C P N apartnessRead : BHist} :
    PositiveRealCarrier R A D W Q H C P N ->
      Cont A D apartnessRead ->
        UnaryHistory apartnessRead /\ Cont A D apartnessRead /\ hsame R R /\
          SemanticNameCert
            (fun row : BHist =>
              List.Mem row (positiveRealFields (PositiveRealUp.mk R A D W Q H C P N)))
            (fun row : BHist =>
              List.Mem row (positiveRealFields (PositiveRealUp.mk R A D W Q H C P N)) /\
                Cont row BHist.Empty row)
            (fun row : BHist =>
              List.Mem row (positiveRealFields (PositiveRealUp.mk R A D W Q H C P N)) /\
                hsame (append row BHist.Empty) row)
            hsame := by
  -- BEDC touchpoint anchor: BHist Cont Empty append hsame SemanticNameCert UnaryHistory
  intro carrier apartnessRoute
  obtain ⟨_realUnary, apartnessUnary, radiusUnary, _windowUnary, _readbackUnary,
    _transportUnary, _replayUnary, _pkgUnary, _nameUnary⟩ := carrier
  have apartnessReadUnary : UnaryHistory apartnessRead :=
    unary_cont_closed apartnessUnary radiusUnary apartnessRoute
  exact
    ⟨apartnessReadUnary, apartnessRoute, hsame_refl R,
      PositiveRealNameCert_obligations (PositiveRealUp.mk R A D W Q H C P N)⟩

end BEDC.Derived.PositiveRealUp
