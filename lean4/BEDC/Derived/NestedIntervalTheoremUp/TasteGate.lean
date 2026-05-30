import BEDC.Derived.NestedIntervalUp
import BEDC.Meta.TasteGate

namespace BEDC.Derived.NestedIntervalTheoremUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def nestedIntervalTheoremEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: nestedIntervalTheoremEncodeBHist h
  | BHist.e1 h => BMark.b1 :: nestedIntervalTheoremEncodeBHist h

def nestedIntervalTheoremDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (nestedIntervalTheoremDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (nestedIntervalTheoremDecodeBHist tail)

private theorem nestedIntervalTheorem_decode_encode_bhist :
    ∀ h : BHist, nestedIntervalTheoremDecodeBHist (nestedIntervalTheoremEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def nestedIntervalTheoremNestedIntervalFields :
    _root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp.mk interval endpoint width schedule regular
      sealRow transportRow provenance cert =>
      [interval, endpoint, width, schedule, regular, sealRow, transportRow, provenance, cert]

def nestedIntervalTheoremFields : _root_.BEDC.Derived.NestedIntervalTheoremUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.NestedIntervalTheoremUp.mk nestedWindow dyadicLedger streamWindow
      regularReadback realSeal =>
      nestedIntervalTheoremNestedIntervalFields nestedWindow ++
        [dyadicLedger, streamWindow, regularReadback, realSeal]

def nestedIntervalTheoremToEventFlow : _root_.BEDC.Derived.NestedIntervalTheoremUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | _root_.BEDC.Derived.NestedIntervalTheoremUp.mk
      (_root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp.mk interval endpoint width schedule
        regular sealRow transportRow provenance cert)
      dyadicLedger streamWindow regularReadback realSeal =>
      [nestedIntervalTheoremEncodeBHist interval,
        nestedIntervalTheoremEncodeBHist endpoint,
        nestedIntervalTheoremEncodeBHist width,
        nestedIntervalTheoremEncodeBHist schedule,
        nestedIntervalTheoremEncodeBHist regular,
        nestedIntervalTheoremEncodeBHist sealRow,
        nestedIntervalTheoremEncodeBHist transportRow,
        nestedIntervalTheoremEncodeBHist provenance,
        nestedIntervalTheoremEncodeBHist cert,
        nestedIntervalTheoremEncodeBHist dyadicLedger,
        nestedIntervalTheoremEncodeBHist streamWindow,
        nestedIntervalTheoremEncodeBHist regularReadback,
        nestedIntervalTheoremEncodeBHist realSeal]

def nestedIntervalTheoremFromEventFlow :
    EventFlow → Option _root_.BEDC.Derived.NestedIntervalTheoremUp
  -- BEDC touchpoint anchor: BHist BMark
  | interval :: restInterval =>
      match restInterval with
      | endpoint :: restEndpoint =>
          match restEndpoint with
          | width :: restWidth =>
              match restWidth with
              | schedule :: restSchedule =>
                  match restSchedule with
                  | regular :: restRegular =>
                      match restRegular with
                      | sealRow :: restSeal =>
                          match restSeal with
                          | transportRow :: restTransport =>
                              match restTransport with
                              | provenance :: restProvenance =>
                                  match restProvenance with
                                  | cert :: restCert =>
                                      match restCert with
                                      | dyadicLedger :: restDyadic =>
                                          match restDyadic with
                                          | streamWindow :: restStream =>
                                              match restStream with
                                              | regularReadback :: restReadback =>
                                                  match restReadback with
                                                  | realSeal :: restSealTail =>
                                                      match restSealTail with
                                                      | [] =>
                                                          some
                                                            (_root_.BEDC.Derived.NestedIntervalTheoremUp.mk
                                                              (_root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp.mk
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  interval)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  endpoint)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  width)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  schedule)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  regular)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  sealRow)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  transportRow)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  provenance)
                                                                (nestedIntervalTheoremDecodeBHist
                                                                  cert))
                                                              (nestedIntervalTheoremDecodeBHist
                                                                dyadicLedger)
                                                              (nestedIntervalTheoremDecodeBHist
                                                                streamWindow)
                                                              (nestedIntervalTheoremDecodeBHist
                                                                regularReadback)
                                                              (nestedIntervalTheoremDecodeBHist
                                                                realSeal))
                                                      | _ :: _ => none
                                                  | [] => none
                                              | [] => none
                                          | [] => none
                                      | [] => none
                                  | [] => none
                              | [] => none
                          | [] => none
                      | [] => none
                  | [] => none
              | [] => none
          | [] => none
      | [] => none
  | [] => none

private theorem nestedIntervalTheorem_round_trip :
    ∀ x : _root_.BEDC.Derived.NestedIntervalTheoremUp,
      nestedIntervalTheoremFromEventFlow (nestedIntervalTheoremToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk nestedWindow dyadicLedger streamWindow regularReadback realSeal =>
      cases nestedWindow with
      | mk interval endpoint width schedule regular sealRow transportRow provenance cert =>
          change
            some
              (_root_.BEDC.Derived.NestedIntervalTheoremUp.mk
                (_root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp.mk
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist interval))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist endpoint))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist width))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist schedule))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist regular))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist sealRow))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist transportRow))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist provenance))
                  (nestedIntervalTheoremDecodeBHist
                    (nestedIntervalTheoremEncodeBHist cert)))
                (nestedIntervalTheoremDecodeBHist
                  (nestedIntervalTheoremEncodeBHist dyadicLedger))
                (nestedIntervalTheoremDecodeBHist
                  (nestedIntervalTheoremEncodeBHist streamWindow))
                (nestedIntervalTheoremDecodeBHist
                  (nestedIntervalTheoremEncodeBHist regularReadback))
                (nestedIntervalTheoremDecodeBHist
                  (nestedIntervalTheoremEncodeBHist realSeal))) =
              some
                (_root_.BEDC.Derived.NestedIntervalTheoremUp.mk
                  (_root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp.mk interval endpoint
                    width schedule regular sealRow transportRow provenance cert)
                  dyadicLedger streamWindow regularReadback realSeal)
          rw [nestedIntervalTheorem_decode_encode_bhist interval,
            nestedIntervalTheorem_decode_encode_bhist endpoint,
            nestedIntervalTheorem_decode_encode_bhist width,
            nestedIntervalTheorem_decode_encode_bhist schedule,
            nestedIntervalTheorem_decode_encode_bhist regular,
            nestedIntervalTheorem_decode_encode_bhist sealRow,
            nestedIntervalTheorem_decode_encode_bhist transportRow,
            nestedIntervalTheorem_decode_encode_bhist provenance,
            nestedIntervalTheorem_decode_encode_bhist cert,
            nestedIntervalTheorem_decode_encode_bhist dyadicLedger,
            nestedIntervalTheorem_decode_encode_bhist streamWindow,
            nestedIntervalTheorem_decode_encode_bhist regularReadback,
            nestedIntervalTheorem_decode_encode_bhist realSeal]

private theorem nestedIntervalTheoremToEventFlow_injective
    {x y : _root_.BEDC.Derived.NestedIntervalTheoremUp} :
    nestedIntervalTheoremToEventFlow x = nestedIntervalTheoremToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have optionEq : some x = some y := by
    calc
      some x = nestedIntervalTheoremFromEventFlow (nestedIntervalTheoremToEventFlow x) :=
        (nestedIntervalTheorem_round_trip x).symm
      _ = nestedIntervalTheoremFromEventFlow (nestedIntervalTheoremToEventFlow y) :=
        congrArg nestedIntervalTheoremFromEventFlow heq
      _ = some y := nestedIntervalTheorem_round_trip y
  exact Option.some.inj optionEq

private theorem nestedIntervalTheorem_field_faithful :
    ∀ x y : _root_.BEDC.Derived.NestedIntervalTheoremUp,
      nestedIntervalTheoremFields x = nestedIntervalTheoremFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk nestedWindow₁ dyadicLedger₁ streamWindow₁ regularReadback₁ realSeal₁ =>
      cases nestedWindow₁ with
      | mk interval₁ endpoint₁ width₁ schedule₁ regular₁ sealRow₁ transportRow₁ provenance₁
          cert₁ =>
          cases y with
          | mk nestedWindow₂ dyadicLedger₂ streamWindow₂ regularReadback₂ realSeal₂ =>
              cases nestedWindow₂ with
              | mk interval₂ endpoint₂ width₂ schedule₂ regular₂ sealRow₂ transportRow₂
                  provenance₂ cert₂ =>
                  cases hfields
                  rfl

instance nestedIntervalTheoremBHistCarrier :
    BHistCarrier _root_.BEDC.Derived.NestedIntervalTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := nestedIntervalTheoremToEventFlow
  fromEventFlow := nestedIntervalTheoremFromEventFlow

instance nestedIntervalTheoremChapterTasteGate :
    ChapterTasteGate _root_.BEDC.Derived.NestedIntervalTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change nestedIntervalTheoremFromEventFlow (nestedIntervalTheoremToEventFlow x) = some x
    exact nestedIntervalTheorem_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (nestedIntervalTheoremToEventFlow_injective heq)

instance nestedIntervalTheoremFieldFaithful :
    FieldFaithful _root_.BEDC.Derived.NestedIntervalTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := nestedIntervalTheoremFields
  field_faithful := nestedIntervalTheorem_field_faithful

instance nestedIntervalTheoremNontrivial :
    BEDC.Meta.TasteGate.Nontrivial _root_.BEDC.Derived.NestedIntervalTheoremUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨_root_.BEDC.Derived.NestedIntervalTheoremUp.mk
        (_root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp.mk BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      _root_.BEDC.Derived.NestedIntervalTheoremUp.mk
        (_root_.BEDC.Derived.NestedIntervalUp.NestedIntervalUp.mk (BHist.e0 BHist.Empty)
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty)
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        injection h with hNested
        injection hNested with hHead
        cases hHead⟩

def taste_gate : ChapterTasteGate _root_.BEDC.Derived.NestedIntervalTheoremUp :=
  -- BEDC touchpoint anchor: BHist BMark
  nestedIntervalTheoremChapterTasteGate

theorem NestedIntervalTheoremTasteGate_single_carrier_alignment :
    (∀ h : BHist, nestedIntervalTheoremDecodeBHist (nestedIntervalTheoremEncodeBHist h) = h) ∧
      (∀ x : _root_.BEDC.Derived.NestedIntervalTheoremUp,
        nestedIntervalTheoremFromEventFlow (nestedIntervalTheoremToEventFlow x) = some x) ∧
        (∀ x y : _root_.BEDC.Derived.NestedIntervalTheoremUp,
          nestedIntervalTheoremToEventFlow x = nestedIntervalTheoremToEventFlow y → x = y) ∧
          nestedIntervalTheoremEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨nestedIntervalTheorem_decode_encode_bhist,
      nestedIntervalTheorem_round_trip,
      (by
        intro x y heq
        exact nestedIntervalTheoremToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.NestedIntervalTheoremUp
