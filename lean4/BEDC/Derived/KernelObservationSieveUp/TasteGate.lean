import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KernelObservationSieveUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KernelObservationSieveUp : Type where
  | mk
      (observerHistory selectorLedger observerFilter acceptedLedger rejectedLedger transport
        continuation provenance nameCert : BHist) :
      KernelObservationSieveUp
  deriving DecidableEq

private def kernelObservationSieveEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: kernelObservationSieveEncodeBHist h
  | BHist.e1 h => BMark.b1 :: kernelObservationSieveEncodeBHist h

private def kernelObservationSieveDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (kernelObservationSieveDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (kernelObservationSieveDecodeBHist tail)

private theorem kernelObservationSieveDecode_encode_bhist :
    ∀ h : BHist,
      kernelObservationSieveDecodeBHist
        (kernelObservationSieveEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem kernelObservationSieve_mk_congr
    {observerHistory observerHistory' selectorLedger selectorLedger'
      observerFilter observerFilter' acceptedLedger acceptedLedger'
      rejectedLedger rejectedLedger' transport transport' continuation continuation'
      provenance provenance' nameCert nameCert' : BHist}
    (hObserverHistory : observerHistory' = observerHistory)
    (hSelectorLedger : selectorLedger' = selectorLedger)
    (hObserverFilter : observerFilter' = observerFilter)
    (hAcceptedLedger : acceptedLedger' = acceptedLedger)
    (hRejectedLedger : rejectedLedger' = rejectedLedger)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hProvenance : provenance' = provenance)
    (hNameCert : nameCert' = nameCert) :
    KernelObservationSieveUp.mk observerHistory' selectorLedger' observerFilter'
        acceptedLedger' rejectedLedger' transport' continuation' provenance' nameCert' =
      KernelObservationSieveUp.mk observerHistory selectorLedger observerFilter
        acceptedLedger rejectedLedger transport continuation provenance nameCert := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hObserverHistory
  cases hSelectorLedger
  cases hObserverFilter
  cases hAcceptedLedger
  cases hRejectedLedger
  cases hTransport
  cases hContinuation
  cases hProvenance
  cases hNameCert
  rfl

private def kernelObservationSieveToEventFlow :
    KernelObservationSieveUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | KernelObservationSieveUp.mk observerHistory selectorLedger observerFilter
      acceptedLedger rejectedLedger transport continuation provenance nameCert =>
      [[BMark.b0],
        kernelObservationSieveEncodeBHist observerHistory,
        [BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist selectorLedger,
        [BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist observerFilter,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist acceptedLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist rejectedLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        kernelObservationSieveEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        kernelObservationSieveEncodeBHist nameCert]

private def kernelObservationSieveFromEventFlow :
    EventFlow → Option KernelObservationSieveUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | observerHistory :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | selectorLedger :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | observerFilter :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | acceptedLedger :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | rejectedLedger :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | continuation :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | provenance :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | nameCert :: rest17 =>
                                                                          match rest17 with
                                                                          | [] =>
                                                                              some
                                                                                (KernelObservationSieveUp.mk
                                                                                  (kernelObservationSieveDecodeBHist observerHistory)
                                                                                  (kernelObservationSieveDecodeBHist selectorLedger)
                                                                                  (kernelObservationSieveDecodeBHist observerFilter)
                                                                                  (kernelObservationSieveDecodeBHist acceptedLedger)
                                                                                  (kernelObservationSieveDecodeBHist rejectedLedger)
                                                                                  (kernelObservationSieveDecodeBHist transport)
                                                                                  (kernelObservationSieveDecodeBHist continuation)
                                                                                  (kernelObservationSieveDecodeBHist provenance)
                                                                                  (kernelObservationSieveDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem kernelObservationSieve_round_trip :
    ∀ x : KernelObservationSieveUp,
      kernelObservationSieveFromEventFlow
        (kernelObservationSieveToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk observerHistory selectorLedger observerFilter acceptedLedger rejectedLedger
      transport continuation provenance nameCert =>
      change
        some
          (KernelObservationSieveUp.mk
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist observerHistory))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist selectorLedger))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist observerFilter))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist acceptedLedger))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist rejectedLedger))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist transport))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist continuation))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist provenance))
            (kernelObservationSieveDecodeBHist
              (kernelObservationSieveEncodeBHist nameCert))) =
          some
            (KernelObservationSieveUp.mk observerHistory selectorLedger
              observerFilter acceptedLedger rejectedLedger transport continuation
              provenance nameCert)
      exact
        congrArg some
          (kernelObservationSieve_mk_congr
            (kernelObservationSieveDecode_encode_bhist observerHistory)
            (kernelObservationSieveDecode_encode_bhist selectorLedger)
            (kernelObservationSieveDecode_encode_bhist observerFilter)
            (kernelObservationSieveDecode_encode_bhist acceptedLedger)
            (kernelObservationSieveDecode_encode_bhist rejectedLedger)
            (kernelObservationSieveDecode_encode_bhist transport)
            (kernelObservationSieveDecode_encode_bhist continuation)
            (kernelObservationSieveDecode_encode_bhist provenance)
            (kernelObservationSieveDecode_encode_bhist nameCert))

private theorem kernelObservationSieveToEventFlow_injective
    {x y : KernelObservationSieveUp} :
    kernelObservationSieveToEventFlow x =
      kernelObservationSieveToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      kernelObservationSieveFromEventFlow
          (kernelObservationSieveToEventFlow x) =
        kernelObservationSieveFromEventFlow
          (kernelObservationSieveToEventFlow y) :=
    congrArg kernelObservationSieveFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (kernelObservationSieve_round_trip x).symm
      (Eq.trans hread (kernelObservationSieve_round_trip y)))

instance kernelObservationSieveBHistCarrier :
    BHistCarrier KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := kernelObservationSieveToEventFlow
  fromEventFlow := kernelObservationSieveFromEventFlow

instance kernelObservationSieveChapterTasteGate :
    ChapterTasteGate KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      kernelObservationSieveFromEventFlow
        (kernelObservationSieveToEventFlow x) = some x
    exact kernelObservationSieve_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (kernelObservationSieveToEventFlow_injective heq)

instance kernelObservationSieveFieldFaithful :
    FieldFaithful KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | KernelObservationSieveUp.mk observerHistory selectorLedger observerFilter
        acceptedLedger rejectedLedger transport continuation provenance nameCert =>
        [observerHistory, selectorLedger, observerFilter, acceptedLedger, rejectedLedger,
          transport, continuation, provenance, nameCert]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk observerHistory selectorLedger observerFilter acceptedLedger rejectedLedger
        transport continuation provenance nameCert =>
        cases y with
        | mk observerHistory' selectorLedger' observerFilter' acceptedLedger'
            rejectedLedger' transport' continuation' provenance' nameCert' =>
            cases hfields
            rfl

instance kernelObservationSieveNontrivial :
    Nontrivial KernelObservationSieveUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨KernelObservationSieveUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      KernelObservationSieveUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem KernelObservationSieveTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      kernelObservationSieveDecodeBHist
        (kernelObservationSieveEncodeBHist h) = h) ∧
      (∀ x : KernelObservationSieveUp,
        kernelObservationSieveFromEventFlow
          (kernelObservationSieveToEventFlow x) = some x) ∧
        (∀ x y : KernelObservationSieveUp,
          kernelObservationSieveToEventFlow x =
            kernelObservationSieveToEventFlow y → x = y) ∧
          kernelObservationSieveEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact kernelObservationSieveDecode_encode_bhist
  · constructor
    · exact kernelObservationSieve_round_trip
    · constructor
      · intro x y heq
        exact kernelObservationSieveToEventFlow_injective heq
      · rfl

end BEDC.Derived.KernelObservationSieveUp
