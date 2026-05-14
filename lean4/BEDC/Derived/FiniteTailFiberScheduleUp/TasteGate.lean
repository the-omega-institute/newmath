import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteTailFiberScheduleUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteTailFiberScheduleUp : Type where
  | mk :
      (tailIndex finiteFiber schedule dyadicLedger regSeqReadback realSeal transport routes
        provenance localName : BHist) →
      FiniteTailFiberScheduleUp
  deriving DecidableEq

def finiteTailFiberScheduleEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteTailFiberScheduleEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteTailFiberScheduleEncodeBHist h

def finiteTailFiberScheduleDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteTailFiberScheduleDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteTailFiberScheduleDecodeBHist tail)

private theorem finiteTailFiberScheduleDecodeEncodeBHist :
    ∀ h : BHist,
      finiteTailFiberScheduleDecodeBHist
        (finiteTailFiberScheduleEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteTailFiberScheduleFields :
    FiniteTailFiberScheduleUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteTailFiberScheduleUp.mk tailIndex finiteFiber schedule dyadicLedger
      regSeqReadback realSeal transport routes provenance localName =>
      [tailIndex, finiteFiber, schedule, dyadicLedger, regSeqReadback, realSeal,
        transport, routes, provenance, localName]

def finiteTailFiberScheduleToEventFlow :
    FiniteTailFiberScheduleUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteTailFiberScheduleFields x).map finiteTailFiberScheduleEncodeBHist

def finiteTailFiberScheduleFromEventFlow :
    EventFlow → Option FiniteTailFiberScheduleUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | tailIndex :: rest0 =>
      match rest0 with
      | [] => none
      | finiteFiber :: rest1 =>
          match rest1 with
          | [] => none
          | schedule :: rest2 =>
              match rest2 with
              | [] => none
              | dyadicLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | regSeqReadback :: rest4 =>
                      match rest4 with
                      | [] => none
                      | realSeal :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | routes :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FiniteTailFiberScheduleUp.mk
                                                  (finiteTailFiberScheduleDecodeBHist tailIndex)
                                                  (finiteTailFiberScheduleDecodeBHist finiteFiber)
                                                  (finiteTailFiberScheduleDecodeBHist schedule)
                                                  (finiteTailFiberScheduleDecodeBHist dyadicLedger)
                                                  (finiteTailFiberScheduleDecodeBHist
                                                    regSeqReadback)
                                                  (finiteTailFiberScheduleDecodeBHist realSeal)
                                                  (finiteTailFiberScheduleDecodeBHist transport)
                                                  (finiteTailFiberScheduleDecodeBHist routes)
                                                  (finiteTailFiberScheduleDecodeBHist provenance)
                                                  (finiteTailFiberScheduleDecodeBHist localName))
                                          | _ :: _ => none

private theorem finiteTailFiberSchedule_mk_congr
    {tailIndex tailIndex' finiteFiber finiteFiber' schedule schedule' dyadicLedger
      dyadicLedger' regSeqReadback regSeqReadback' realSeal realSeal' transport transport'
      routes routes' provenance provenance' localName localName' : BHist} :
    tailIndex = tailIndex' →
      finiteFiber = finiteFiber' →
        schedule = schedule' →
          dyadicLedger = dyadicLedger' →
            regSeqReadback = regSeqReadback' →
              realSeal = realSeal' →
                transport = transport' →
                  routes = routes' →
                    provenance = provenance' →
                      localName = localName' →
                        FiniteTailFiberScheduleUp.mk tailIndex finiteFiber schedule
                            dyadicLedger regSeqReadback realSeal transport routes provenance
                            localName =
                          FiniteTailFiberScheduleUp.mk tailIndex' finiteFiber' schedule'
                            dyadicLedger' regSeqReadback' realSeal' transport' routes'
                            provenance' localName' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro htailIndex hfiniteFiber hschedule hdyadicLedger hregSeqReadback hrealSeal htransport
    hroutes hprovenance hlocalName
  cases htailIndex
  cases hfiniteFiber
  cases hschedule
  cases hdyadicLedger
  cases hregSeqReadback
  cases hrealSeal
  cases htransport
  cases hroutes
  cases hprovenance
  cases hlocalName
  rfl

private theorem finiteTailFiberSchedule_round_trip :
    ∀ x : FiniteTailFiberScheduleUp,
      finiteTailFiberScheduleFromEventFlow
          (finiteTailFiberScheduleToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk tailIndex finiteFiber schedule dyadicLedger regSeqReadback realSeal transport routes
      provenance localName =>
      change
        some
            (FiniteTailFiberScheduleUp.mk
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist tailIndex))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist finiteFiber))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist schedule))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist dyadicLedger))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist regSeqReadback))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist realSeal))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist transport))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist routes))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist provenance))
              (finiteTailFiberScheduleDecodeBHist
                (finiteTailFiberScheduleEncodeBHist localName))) =
          some
            (FiniteTailFiberScheduleUp.mk tailIndex finiteFiber schedule dyadicLedger
              regSeqReadback realSeal transport routes provenance localName)
      exact congrArg some
        (finiteTailFiberSchedule_mk_congr
          (finiteTailFiberScheduleDecodeEncodeBHist tailIndex)
          (finiteTailFiberScheduleDecodeEncodeBHist finiteFiber)
          (finiteTailFiberScheduleDecodeEncodeBHist schedule)
          (finiteTailFiberScheduleDecodeEncodeBHist dyadicLedger)
          (finiteTailFiberScheduleDecodeEncodeBHist regSeqReadback)
          (finiteTailFiberScheduleDecodeEncodeBHist realSeal)
          (finiteTailFiberScheduleDecodeEncodeBHist transport)
          (finiteTailFiberScheduleDecodeEncodeBHist routes)
          (finiteTailFiberScheduleDecodeEncodeBHist provenance)
          (finiteTailFiberScheduleDecodeEncodeBHist localName))

private theorem finiteTailFiberScheduleToEventFlow_injective
    {x y : FiniteTailFiberScheduleUp} :
    finiteTailFiberScheduleToEventFlow x =
      finiteTailFiberScheduleToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteTailFiberScheduleFromEventFlow
          (finiteTailFiberScheduleToEventFlow x) =
        finiteTailFiberScheduleFromEventFlow
          (finiteTailFiberScheduleToEventFlow y) :=
    congrArg finiteTailFiberScheduleFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteTailFiberSchedule_round_trip x).symm
      (Eq.trans hread (finiteTailFiberSchedule_round_trip y)))

private theorem finiteTailFiberSchedule_fields_faithful :
    ∀ x y : FiniteTailFiberScheduleUp,
      finiteTailFiberScheduleFields x = finiteTailFiberScheduleFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk tailIndex finiteFiber schedule dyadicLedger regSeqReadback realSeal transport routes
      provenance localName =>
      cases y with
      | mk tailIndex' finiteFiber' schedule' dyadicLedger' regSeqReadback' realSeal'
          transport' routes' provenance' localName' =>
          cases hfields
          rfl

instance finiteTailFiberScheduleBHistCarrier :
    BHistCarrier FiniteTailFiberScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteTailFiberScheduleToEventFlow
  fromEventFlow := finiteTailFiberScheduleFromEventFlow

instance finiteTailFiberScheduleChapterTasteGate :
    ChapterTasteGate FiniteTailFiberScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteTailFiberScheduleFromEventFlow
        (finiteTailFiberScheduleToEventFlow x) = some x
    exact finiteTailFiberSchedule_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteTailFiberScheduleToEventFlow_injective heq)

instance finiteTailFiberScheduleFieldFaithful :
    FieldFaithful FiniteTailFiberScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteTailFiberScheduleFields
  field_faithful := finiteTailFiberSchedule_fields_faithful

instance finiteTailFiberScheduleNontrivial :
    Nontrivial FiniteTailFiberScheduleUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteTailFiberScheduleUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteTailFiberScheduleUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteTailFiberScheduleUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteTailFiberScheduleChapterTasteGate

theorem FiniteTailFiberScheduleTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      finiteTailFiberScheduleDecodeBHist (finiteTailFiberScheduleEncodeBHist h) = h) ∧
      (∀ x : FiniteTailFiberScheduleUp,
        finiteTailFiberScheduleFromEventFlow (finiteTailFiberScheduleToEventFlow x) =
          some x) ∧
        (∀ x y : FiniteTailFiberScheduleUp,
          finiteTailFiberScheduleToEventFlow x = finiteTailFiberScheduleToEventFlow y →
            x = y) ∧
          finiteTailFiberScheduleEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∀ x y : FiniteTailFiberScheduleUp,
              finiteTailFiberScheduleFields x = finiteTailFiberScheduleFields y → x = y) ∧
              (∃ x y : FiniteTailFiberScheduleUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact finiteTailFiberScheduleDecodeEncodeBHist
  · constructor
    · exact finiteTailFiberSchedule_round_trip
    · constructor
      · intro x y heq
        exact finiteTailFiberScheduleToEventFlow_injective heq
      · constructor
        · rfl
        · constructor
          · exact finiteTailFiberSchedule_fields_faithful
          · exact
              ⟨FiniteTailFiberScheduleUp.mk BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty,
                FiniteTailFiberScheduleUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty,
                by
                  intro h
                  cases h⟩

end BEDC.Derived.FiniteTailFiberScheduleUp
