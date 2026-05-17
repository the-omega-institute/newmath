import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.StatusDowngradeUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive StatusDowngradeUp : Type where
  | mk
      (prior failure lowered gap route report transport replay provenance name : BHist) :
      StatusDowngradeUp
  deriving DecidableEq

def statusDowngradeEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: statusDowngradeEncodeBHist h
  | BHist.e1 h => BMark.b1 :: statusDowngradeEncodeBHist h

def statusDowngradeDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (statusDowngradeDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (statusDowngradeDecodeBHist tail)

private theorem statusDowngrade_decode_encode_bhist :
    ∀ h : BHist, statusDowngradeDecodeBHist (statusDowngradeEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def statusDowngradeToEventFlow : StatusDowngradeUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | StatusDowngradeUp.mk prior failure lowered gap route report transport replay provenance name =>
      [[BMark.b1, BMark.b0, BMark.b0, BMark.b1],
        statusDowngradeEncodeBHist prior,
        statusDowngradeEncodeBHist failure,
        statusDowngradeEncodeBHist lowered,
        statusDowngradeEncodeBHist gap,
        statusDowngradeEncodeBHist route,
        statusDowngradeEncodeBHist report,
        statusDowngradeEncodeBHist transport,
        statusDowngradeEncodeBHist replay,
        statusDowngradeEncodeBHist provenance,
        statusDowngradeEncodeBHist name]

def statusDowngradeFromEventFlow : EventFlow → Option StatusDowngradeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | _tag :: prior :: failure :: lowered :: gap :: route :: report :: transport :: replay ::
      provenance :: name :: [] =>
      some
        (StatusDowngradeUp.mk
          (statusDowngradeDecodeBHist prior)
          (statusDowngradeDecodeBHist failure)
          (statusDowngradeDecodeBHist lowered)
          (statusDowngradeDecodeBHist gap)
          (statusDowngradeDecodeBHist route)
          (statusDowngradeDecodeBHist report)
          (statusDowngradeDecodeBHist transport)
          (statusDowngradeDecodeBHist replay)
          (statusDowngradeDecodeBHist provenance)
          (statusDowngradeDecodeBHist name))
  | _ => none

def statusDowngradeFields : StatusDowngradeUp → List BHist :=
  -- BEDC touchpoint anchor: BHist BMark
  fun
  | StatusDowngradeUp.mk prior failure lowered gap route report transport replay provenance name =>
      [prior, failure, lowered, gap, route, report, transport, replay, provenance, name]

private theorem statusDowngrade_round_trip :
    ∀ x : StatusDowngradeUp,
      statusDowngradeFromEventFlow (statusDowngradeToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk prior failure lowered gap route report transport replay provenance name =>
      simp only [statusDowngradeToEventFlow, statusDowngradeFromEventFlow,
        statusDowngrade_decode_encode_bhist]

private theorem statusDowngradeToEventFlow_injective {x y : StatusDowngradeUp} :
    statusDowngradeToEventFlow x = statusDowngradeToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      statusDowngradeFromEventFlow (statusDowngradeToEventFlow x) =
        statusDowngradeFromEventFlow (statusDowngradeToEventFlow y) :=
    congrArg statusDowngradeFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (statusDowngrade_round_trip x).symm
      (Eq.trans hread (statusDowngrade_round_trip y)))

instance statusDowngradeBHistCarrier : BHistCarrier StatusDowngradeUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := statusDowngradeToEventFlow
  fromEventFlow := statusDowngradeFromEventFlow

instance statusDowngradeChapterTasteGate : ChapterTasteGate StatusDowngradeUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change statusDowngradeFromEventFlow (statusDowngradeToEventFlow x) = some x
    exact statusDowngrade_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (statusDowngradeToEventFlow_injective heq)

def taste_gate : ChapterTasteGate StatusDowngradeUp :=
  -- BEDC touchpoint anchor: BHist BMark
  statusDowngradeChapterTasteGate

instance statusDowngradeFieldFaithful : FieldFaithful StatusDowngradeUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := statusDowngradeFields
  field_faithful := by
    intro x y h
    cases x with
    | mk prior1 failure1 lowered1 gap1 route1 report1 transport1 replay1 provenance1 name1 =>
        cases y with
        | mk prior2 failure2 lowered2 gap2 route2 report2 transport2 replay2 provenance2 name2 =>
            injection h with hPrior t1
            injection t1 with hFailure t2
            injection t2 with hLowered t3
            injection t3 with hGap t4
            injection t4 with hRoute t5
            injection t5 with hReport t6
            injection t6 with hTransport t7
            injection t7 with hReplay t8
            injection t8 with hProvenance t9
            injection t9 with hName _
            cases hPrior
            cases hFailure
            cases hLowered
            cases hGap
            cases hRoute
            cases hReport
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

instance statusDowngradeNontrivial :
    BEDC.Meta.TasteGate.Nontrivial StatusDowngradeUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨StatusDowngradeUp.mk
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      StatusDowngradeUp.mk
        (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

end BEDC.Derived.StatusDowngradeUp
