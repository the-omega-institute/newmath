import BEDC.Derived.ModulusCompositionScheduleUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ModulusCompositionScheduleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ModulusCompositionScheduleUp : Type where
  | mk (mu nu Wmu Wnu epsilon delta R A E H C P N : BHist) : ModulusCompositionScheduleUp
  deriving DecidableEq

def modulusCompositionScheduleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: modulusCompositionScheduleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: modulusCompositionScheduleEncodeBHist h

def modulusCompositionScheduleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (modulusCompositionScheduleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (modulusCompositionScheduleDecodeBHist tail)

private theorem ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist,
      modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def modulusCompositionScheduleFields : ModulusCompositionScheduleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ModulusCompositionScheduleUp.mk mu nu Wmu Wnu epsilon delta R A E H C P N =>
      [mu, nu, Wmu, Wnu, epsilon, delta, R, A, E, H, C, P, N]

def modulusCompositionScheduleToEventFlow : ModulusCompositionScheduleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (modulusCompositionScheduleFields x).map modulusCompositionScheduleEncodeBHist

private def modulusCompositionScheduleEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => modulusCompositionScheduleEventAtDefault index rest

def modulusCompositionScheduleFromEventFlow :
    EventFlow → Option ModulusCompositionScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun ef =>
    some
      (ModulusCompositionScheduleUp.mk
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 0 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 1 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 2 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 3 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 4 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 5 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 6 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 7 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 8 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 9 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 10 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 11 ef))
        (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEventAtDefault 12 ef)))

private theorem ModulusCompositionScheduleTasteGate_single_carrier_alignment_round_trip :
    ∀ x : ModulusCompositionScheduleUp,
      modulusCompositionScheduleFromEventFlow (modulusCompositionScheduleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk mu nu Wmu Wnu epsilon delta R A E H C P N =>
      change
        some
          (ModulusCompositionScheduleUp.mk
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist mu))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist nu))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist Wmu))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist Wnu))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist epsilon))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist delta))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist R))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist A))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist E))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist H))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist C))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist P))
            (modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist N))) =
          some (ModulusCompositionScheduleUp.mk mu nu Wmu Wnu epsilon delta R A E H C P N)
      rw [ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode mu,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode nu,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode Wmu,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode Wnu,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode epsilon,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode delta,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode R,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode A,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode E,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode H,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode C,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode P,
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode N]

private theorem ModulusCompositionScheduleTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : ModulusCompositionScheduleUp} :
    modulusCompositionScheduleToEventFlow x = modulusCompositionScheduleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      modulusCompositionScheduleFromEventFlow (modulusCompositionScheduleToEventFlow x) =
        modulusCompositionScheduleFromEventFlow (modulusCompositionScheduleToEventFlow y) :=
    congrArg modulusCompositionScheduleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (ModulusCompositionScheduleTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (ModulusCompositionScheduleTasteGate_single_carrier_alignment_round_trip y)))

private theorem ModulusCompositionScheduleTasteGate_single_carrier_alignment_fields :
    ∀ x y : ModulusCompositionScheduleUp,
      modulusCompositionScheduleFields x = modulusCompositionScheduleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk mu1 nu1 Wmu1 Wnu1 epsilon1 delta1 R1 A1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk mu2 nu2 Wmu2 Wnu2 epsilon2 delta2 R2 A2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance modulusCompositionScheduleBHistCarrier :
    BHistCarrier ModulusCompositionScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := modulusCompositionScheduleToEventFlow
  fromEventFlow := modulusCompositionScheduleFromEventFlow

instance modulusCompositionScheduleChapterTasteGate :
    ChapterTasteGate ModulusCompositionScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      modulusCompositionScheduleFromEventFlow (modulusCompositionScheduleToEventFlow x) =
        some x
    exact ModulusCompositionScheduleTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (ModulusCompositionScheduleTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance modulusCompositionScheduleFieldFaithful :
    FieldFaithful ModulusCompositionScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := modulusCompositionScheduleFields
  field_faithful := ModulusCompositionScheduleTasteGate_single_carrier_alignment_fields

instance modulusCompositionScheduleNontrivial :
    BEDC.Meta.TasteGate.Nontrivial ModulusCompositionScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ModulusCompositionScheduleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      ModulusCompositionScheduleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ModulusCompositionScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  modulusCompositionScheduleChapterTasteGate

theorem ModulusCompositionScheduleTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate ModulusCompositionScheduleUp) ∧
      Nonempty (FieldFaithful ModulusCompositionScheduleUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial ModulusCompositionScheduleUp) ∧
          (∀ h : BHist,
            modulusCompositionScheduleDecodeBHist (modulusCompositionScheduleEncodeBHist h) = h) ∧
            (∀ x : ModulusCompositionScheduleUp,
              modulusCompositionScheduleFromEventFlow (modulusCompositionScheduleToEventFlow x) =
                some x) ∧
              (∀ x y : ModulusCompositionScheduleUp,
                modulusCompositionScheduleToEventFlow x =
                    modulusCompositionScheduleToEventFlow y →
                  x = y) ∧
                modulusCompositionScheduleEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨⟨modulusCompositionScheduleChapterTasteGate⟩,
      ⟨modulusCompositionScheduleFieldFaithful⟩,
      ⟨modulusCompositionScheduleNontrivial⟩,
      ModulusCompositionScheduleTasteGate_single_carrier_alignment_decode,
      ModulusCompositionScheduleTasteGate_single_carrier_alignment_round_trip,
      (fun _ _ heq =>
        ModulusCompositionScheduleTasteGate_single_carrier_alignment_toEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.ModulusCompositionScheduleUp
