import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LowerRealUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LowerRealUp : Type where
  | mk (L W R E H C P N : BHist) : LowerRealUp
  deriving DecidableEq

def lowerRealEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: lowerRealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: lowerRealEncodeBHist h

def lowerRealDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (lowerRealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (lowerRealDecodeBHist tail)

private theorem LowerRealTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist, lowerRealDecodeBHist (lowerRealEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def lowerRealFields : LowerRealUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LowerRealUp.mk L W R E H C P N => [L, W, R, E, H, C, P, N]

def lowerRealToEventFlow : LowerRealUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (lowerRealFields x).map lowerRealEncodeBHist

private def LowerRealTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      LowerRealTasteGate_single_carrier_alignment_eventAt index rest

def lowerRealFromEventFlow (ef : EventFlow) : Option LowerRealUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (LowerRealUp.mk
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 0 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 1 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 2 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 3 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 4 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 5 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 6 ef))
      (lowerRealDecodeBHist (LowerRealTasteGate_single_carrier_alignment_eventAt 7 ef)))

private theorem LowerRealTasteGate_single_carrier_alignment_round_trip
    (x : LowerRealUp) :
    lowerRealFromEventFlow (lowerRealToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk L W R E H C P N =>
      change
        some
          (LowerRealUp.mk
            (lowerRealDecodeBHist (lowerRealEncodeBHist L))
            (lowerRealDecodeBHist (lowerRealEncodeBHist W))
            (lowerRealDecodeBHist (lowerRealEncodeBHist R))
            (lowerRealDecodeBHist (lowerRealEncodeBHist E))
            (lowerRealDecodeBHist (lowerRealEncodeBHist H))
            (lowerRealDecodeBHist (lowerRealEncodeBHist C))
            (lowerRealDecodeBHist (lowerRealEncodeBHist P))
            (lowerRealDecodeBHist (lowerRealEncodeBHist N))) =
          some (LowerRealUp.mk L W R E H C P N)
      rw [LowerRealTasteGate_single_carrier_alignment_decode_encode L,
        LowerRealTasteGate_single_carrier_alignment_decode_encode W,
        LowerRealTasteGate_single_carrier_alignment_decode_encode R,
        LowerRealTasteGate_single_carrier_alignment_decode_encode E,
        LowerRealTasteGate_single_carrier_alignment_decode_encode H,
        LowerRealTasteGate_single_carrier_alignment_decode_encode C,
        LowerRealTasteGate_single_carrier_alignment_decode_encode P,
        LowerRealTasteGate_single_carrier_alignment_decode_encode N]

private theorem LowerRealTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : LowerRealUp} :
    lowerRealToEventFlow x = lowerRealToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      lowerRealFromEventFlow (lowerRealToEventFlow x) =
        lowerRealFromEventFlow (lowerRealToEventFlow y) :=
    congrArg lowerRealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (LowerRealTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (LowerRealTasteGate_single_carrier_alignment_round_trip y)))

private theorem LowerRealTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : LowerRealUp, lowerRealFields x = lowerRealFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk L₁ W₁ R₁ E₁ H₁ C₁ P₁ N₁ =>
      cases y with
      | mk L₂ W₂ R₂ E₂ H₂ C₂ P₂ N₂ =>
          cases hfields
          rfl

instance lowerRealBHistCarrier : BHistCarrier LowerRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := lowerRealToEventFlow
  fromEventFlow := lowerRealFromEventFlow

instance lowerRealChapterTasteGate : ChapterTasteGate LowerRealUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change lowerRealFromEventFlow (lowerRealToEventFlow x) = some x
    exact LowerRealTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (LowerRealTasteGate_single_carrier_alignment_toEventFlow_injective heq)

theorem LowerRealTasteGate_single_carrier_alignment :
    (∀ h : BHist, lowerRealDecodeBHist (lowerRealEncodeBHist h) = h) ∧
      (∀ x : LowerRealUp, lowerRealFromEventFlow (lowerRealToEventFlow x) = some x) ∧
        (∀ x y : LowerRealUp, lowerRealToEventFlow x = lowerRealToEventFlow y → x = y) ∧
          lowerRealEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : LowerRealUp, lowerRealFields x = lowerRealFields y → x = y) ∧
              (∃ x y : LowerRealUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨LowerRealTasteGate_single_carrier_alignment_decode_encode,
      LowerRealTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq => LowerRealTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl,
      LowerRealTasteGate_single_carrier_alignment_fields_faithful,
      ⟨LowerRealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        LowerRealUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
        by
          intro h
          cases h⟩⟩

theorem LowerRealCarrier_namecert_obligations (x : LowerRealUp) :
    ∃ L0 W R E H C P N : BHist,
      x = LowerRealUp.mk L0 W R E H C P N ∧
        lowerRealFields x = [L0, W, R, E, H, C, P, N] ∧
          lowerRealEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark NameCert
  cases x with
  | mk L0 W R E H C P N =>
      exact ⟨L0, W, R, E, H, C, P, N, rfl, rfl, rfl⟩

theorem LowerRealCarrier_realup_handoff
    {L0 W R E H C P N windowRead sealRead : BHist} :
    lowerRealFields (LowerRealUp.mk L0 W R E H C P N) = [L0, W, R, E, H, C, P, N] →
      UnaryHistory W →
        UnaryHistory R →
          UnaryHistory E →
            Cont W R windowRead →
              Cont windowRead E sealRead →
                UnaryHistory windowRead ∧
                  UnaryHistory sealRead ∧
                    Cont W R windowRead ∧
                      Cont windowRead E sealRead ∧
                        hsame (lowerRealDecodeBHist (lowerRealEncodeBHist E)) E := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont hsame
  intro fieldRows windowUnary handoffUnary sealUnary windowRoute sealRoute
  cases fieldRows
  have windowReadUnary : UnaryHistory windowRead :=
    unary_cont_closed windowUnary handoffUnary windowRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowReadUnary sealUnary sealRoute
  have sealDecode :
      hsame (lowerRealDecodeBHist (lowerRealEncodeBHist E)) E := by
    change lowerRealDecodeBHist (lowerRealEncodeBHist E) = E
    exact LowerRealTasteGate_single_carrier_alignment_decode_encode E
  exact ⟨windowReadUnary, sealReadUnary, windowRoute, sealRoute, sealDecode⟩

end BEDC.Derived.LowerRealUp
