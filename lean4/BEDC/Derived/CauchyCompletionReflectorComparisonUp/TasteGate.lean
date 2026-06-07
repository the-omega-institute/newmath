import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyCompletionReflectorComparisonUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyCompletionReflectorComparisonUp : Type where
  | mk (rho K0 A M W Q D E H C P N : BHist) : CauchyCompletionReflectorComparisonUp
  deriving DecidableEq

def cauchyCompletionReflectorComparisonEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyCompletionReflectorComparisonEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyCompletionReflectorComparisonEncodeBHist h

def cauchyCompletionReflectorComparisonDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyCompletionReflectorComparisonDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyCompletionReflectorComparisonDecodeBHist tail)

private theorem CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyCompletionReflectorComparisonDecodeBHist
        (cauchyCompletionReflectorComparisonEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyCompletionReflectorComparisonFields :
    CauchyCompletionReflectorComparisonUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyCompletionReflectorComparisonUp.mk rho K0 A M W Q D E H C P N =>
      [rho, K0, A, M, W, Q, D, E, H, C, P, N]

def cauchyCompletionReflectorComparisonToEventFlow :
    CauchyCompletionReflectorComparisonUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x =>
    (cauchyCompletionReflectorComparisonFields x).map
      cauchyCompletionReflectorComparisonEncodeBHist

private def cauchyCompletionReflectorComparisonEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyCompletionReflectorComparisonEventAtDefault index rest

def cauchyCompletionReflectorComparisonFromEventFlow :
    EventFlow → Option CauchyCompletionReflectorComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (CauchyCompletionReflectorComparisonUp.mk
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 0 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 1 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 2 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 3 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 4 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 5 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 6 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 7 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 8 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 9 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 10 ef))
        (cauchyCompletionReflectorComparisonDecodeBHist
          (cauchyCompletionReflectorComparisonEventAtDefault 11 ef)))

private theorem CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyCompletionReflectorComparisonUp,
      cauchyCompletionReflectorComparisonFromEventFlow
        (cauchyCompletionReflectorComparisonToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk rho K0 A M W Q D E H C P N =>
      change
        some
          (CauchyCompletionReflectorComparisonUp.mk
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist rho))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist K0))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist A))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist M))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist W))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist Q))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist D))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist E))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist H))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist C))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist P))
            (cauchyCompletionReflectorComparisonDecodeBHist
              (cauchyCompletionReflectorComparisonEncodeBHist N))) =
          some (CauchyCompletionReflectorComparisonUp.mk rho K0 A M W Q D E H C P N)
      rw [CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode rho,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode K0,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode A,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode M,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode W,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode Q,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode D,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode E,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode H,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode C,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode P,
        CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode N]

private theorem CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyCompletionReflectorComparisonUp} :
    cauchyCompletionReflectorComparisonToEventFlow x =
      cauchyCompletionReflectorComparisonToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyCompletionReflectorComparisonFromEventFlow
          (cauchyCompletionReflectorComparisonToEventFlow x) =
        cauchyCompletionReflectorComparisonFromEventFlow
          (cauchyCompletionReflectorComparisonToEventFlow y) :=
    congrArg cauchyCompletionReflectorComparisonFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyCompletionReflectorComparisonBHistCarrier :
    BHistCarrier CauchyCompletionReflectorComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyCompletionReflectorComparisonToEventFlow
  fromEventFlow := cauchyCompletionReflectorComparisonFromEventFlow

instance cauchyCompletionReflectorComparisonChapterTasteGate :
    ChapterTasteGate CauchyCompletionReflectorComparisonUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      cauchyCompletionReflectorComparisonFromEventFlow
        (cauchyCompletionReflectorComparisonToEventFlow x) = some x
    exact CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

def taste_gate : ChapterTasteGate CauchyCompletionReflectorComparisonUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyCompletionReflectorComparisonChapterTasteGate

theorem CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      cauchyCompletionReflectorComparisonDecodeBHist
        (cauchyCompletionReflectorComparisonEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier CauchyCompletionReflectorComparisonUp) ∧
        Nonempty (ChapterTasteGate CauchyCompletionReflectorComparisonUp) ∧
          cauchyCompletionReflectorComparisonEncodeBHist BHist.Empty =
            ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨CauchyCompletionReflectorComparisonTasteGate_single_carrier_alignment_decode,
      ⟨cauchyCompletionReflectorComparisonBHistCarrier⟩,
      ⟨cauchyCompletionReflectorComparisonChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.CauchyCompletionReflectorComparisonUp
