import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyRateNormalFormUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CauchyRateNormalFormUp : Type where
  | mk (q rho nu D S G E H C P N : BHist) : CauchyRateNormalFormUp
  deriving DecidableEq

def cauchyRateNormalFormEncodeBHist : BHist → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyRateNormalFormEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyRateNormalFormEncodeBHist h

def cauchyRateNormalFormDecodeBHist : List BMark → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyRateNormalFormDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyRateNormalFormDecodeBHist tail)

private theorem CauchyRateNormalFormTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyRateNormalFormFields : CauchyRateNormalFormUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyRateNormalFormUp.mk q rho nu D S G E H C P N => [q, rho, nu, D, S, G, E, H, C, P, N]

def cauchyRateNormalFormToEventFlow : CauchyRateNormalFormUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (cauchyRateNormalFormFields x).map cauchyRateNormalFormEncodeBHist

private def cauchyRateNormalFormEventAtDefault : Nat → EventFlow → List BMark
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyRateNormalFormEventAtDefault index rest

def cauchyRateNormalFormFromEventFlow (ef : EventFlow) : Option CauchyRateNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyRateNormalFormUp.mk
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 0 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 1 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 2 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 3 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 4 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 5 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 6 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 7 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 8 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 9 ef))
      (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEventAtDefault 10 ef)))

private theorem CauchyRateNormalFormTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CauchyRateNormalFormUp,
      cauchyRateNormalFormFromEventFlow (cauchyRateNormalFormToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk q rho nu D S G E H C P N =>
      change
        some
          (CauchyRateNormalFormUp.mk
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist q))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist rho))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist nu))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist D))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist S))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist G))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist E))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist H))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist C))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist P))
            (cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist N))) =
          some (CauchyRateNormalFormUp.mk q rho nu D S G E H C P N)
      rw [CauchyRateNormalFormTasteGate_single_carrier_alignment_decode q,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode rho,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode nu,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode D,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode S,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode G,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode E,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode H,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode C,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode P,
        CauchyRateNormalFormTasteGate_single_carrier_alignment_decode N]

private theorem CauchyRateNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CauchyRateNormalFormUp} :
    cauchyRateNormalFormToEventFlow x = cauchyRateNormalFormToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyRateNormalFormFromEventFlow (cauchyRateNormalFormToEventFlow x) =
        cauchyRateNormalFormFromEventFlow (cauchyRateNormalFormToEventFlow y) :=
    congrArg cauchyRateNormalFormFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (CauchyRateNormalFormTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CauchyRateNormalFormTasteGate_single_carrier_alignment_round_trip y)))

instance cauchyRateNormalFormBHistCarrier : BHistCarrier CauchyRateNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyRateNormalFormToEventFlow
  fromEventFlow := cauchyRateNormalFormFromEventFlow

instance cauchyRateNormalFormChapterTasteGate : ChapterTasteGate CauchyRateNormalFormUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cauchyRateNormalFormFromEventFlow (cauchyRateNormalFormToEventFlow x) = some x
    exact CauchyRateNormalFormTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyRateNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def taste_gate : ChapterTasteGate CauchyRateNormalFormUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cauchyRateNormalFormChapterTasteGate

theorem CauchyRateNormalFormTasteGate_single_carrier_alignment :
    (∀ h : BHist, cauchyRateNormalFormDecodeBHist (cauchyRateNormalFormEncodeBHist h) = h) ∧
      (∀ x : CauchyRateNormalFormUp,
        cauchyRateNormalFormFromEventFlow (cauchyRateNormalFormToEventFlow x) = some x) ∧
        (∀ x y : CauchyRateNormalFormUp,
          cauchyRateNormalFormToEventFlow x = cauchyRateNormalFormToEventFlow y → x = y) ∧
          cauchyRateNormalFormEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨CauchyRateNormalFormTasteGate_single_carrier_alignment_decode,
      CauchyRateNormalFormTasteGate_single_carrier_alignment_round_trip,
      fun x y heq => CauchyRateNormalFormTasteGate_single_carrier_alignment_toEventFlow_injective heq,
      rfl⟩

end BEDC.Derived.CauchyRateNormalFormUp
