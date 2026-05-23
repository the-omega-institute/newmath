import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedCauchyFilterUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedCauchyFilterUp : Type where
  | mk
      (filter basis regular stream readback dyadic locatedTail realSeal transport continuation
        provenance localNameCert : BHist) :
        LocatedCauchyFilterUp
  deriving DecidableEq

def locatedCauchyFilterEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedCauchyFilterEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedCauchyFilterEncodeBHist h

def locatedCauchyFilterDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedCauchyFilterDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedCauchyFilterDecodeBHist tail)

private theorem locatedCauchyFilterDecode_encode_bhist :
    ∀ h : BHist,
      locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def locatedCauchyFilterFields : LocatedCauchyFilterUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyFilterUp.mk filter basis regular stream readback dyadic locatedTail realSeal
      transport continuation provenance localNameCert =>
      [filter, basis, regular, stream, readback, dyadic, locatedTail, realSeal, transport,
        continuation, provenance, localNameCert]

def locatedCauchyFilterToEventFlow : LocatedCauchyFilterUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedCauchyFilterUp.mk filter basis regular stream readback dyadic locatedTail realSeal
      transport continuation provenance localNameCert =>
      [[BMark.b1, BMark.b0, BMark.b1, BMark.b0],
        locatedCauchyFilterEncodeBHist filter,
        locatedCauchyFilterEncodeBHist basis,
        locatedCauchyFilterEncodeBHist regular,
        locatedCauchyFilterEncodeBHist stream,
        locatedCauchyFilterEncodeBHist readback,
        locatedCauchyFilterEncodeBHist dyadic,
        locatedCauchyFilterEncodeBHist locatedTail,
        locatedCauchyFilterEncodeBHist realSeal,
        locatedCauchyFilterEncodeBHist transport,
        locatedCauchyFilterEncodeBHist continuation,
        locatedCauchyFilterEncodeBHist provenance,
        locatedCauchyFilterEncodeBHist localNameCert]

def locatedCauchyFilterFromEventFlow : EventFlow → Option LocatedCauchyFilterUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | filter :: rest1 =>
          match rest1 with
          | [] => none
          | basis :: rest2 =>
              match rest2 with
              | [] => none
              | regular :: rest3 =>
                  match rest3 with
                  | [] => none
                  | stream :: rest4 =>
                      match rest4 with
                      | [] => none
                      | readback :: rest5 =>
                          match rest5 with
                          | [] => none
                          | dyadic :: rest6 =>
                              match rest6 with
                              | [] => none
                              | locatedTail :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | realSeal :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | continuation :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | provenance :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | localNameCert :: rest12 =>
                                                      match rest12 with
                                                      | [] =>
                                                          some
                                                            (LocatedCauchyFilterUp.mk
                                                              (locatedCauchyFilterDecodeBHist
                                                                filter)
                                                              (locatedCauchyFilterDecodeBHist
                                                                basis)
                                                              (locatedCauchyFilterDecodeBHist
                                                                regular)
                                                              (locatedCauchyFilterDecodeBHist
                                                                stream)
                                                              (locatedCauchyFilterDecodeBHist
                                                                readback)
                                                              (locatedCauchyFilterDecodeBHist
                                                                dyadic)
                                                              (locatedCauchyFilterDecodeBHist
                                                                locatedTail)
                                                              (locatedCauchyFilterDecodeBHist
                                                                realSeal)
                                                              (locatedCauchyFilterDecodeBHist
                                                                transport)
                                                              (locatedCauchyFilterDecodeBHist
                                                                continuation)
                                                              (locatedCauchyFilterDecodeBHist
                                                                provenance)
                                                              (locatedCauchyFilterDecodeBHist
                                                                localNameCert))
                                                      | _ :: _ => none

private theorem locatedCauchyFilter_round_trip :
    ∀ x : LocatedCauchyFilterUp,
      locatedCauchyFilterFromEventFlow (locatedCauchyFilterToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk filter basis regular stream readback dyadic locatedTail realSeal transport continuation
      provenance localNameCert =>
      change
        some
            (LocatedCauchyFilterUp.mk
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist filter))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist basis))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist regular))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist stream))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist readback))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist dyadic))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist locatedTail))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist realSeal))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist transport))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist continuation))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist provenance))
              (locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist localNameCert))) =
          some
            (LocatedCauchyFilterUp.mk filter basis regular stream readback dyadic locatedTail
              realSeal transport continuation provenance localNameCert)
      rw [locatedCauchyFilterDecode_encode_bhist filter,
        locatedCauchyFilterDecode_encode_bhist basis,
        locatedCauchyFilterDecode_encode_bhist regular,
        locatedCauchyFilterDecode_encode_bhist stream,
        locatedCauchyFilterDecode_encode_bhist readback,
        locatedCauchyFilterDecode_encode_bhist dyadic,
        locatedCauchyFilterDecode_encode_bhist locatedTail,
        locatedCauchyFilterDecode_encode_bhist realSeal,
        locatedCauchyFilterDecode_encode_bhist transport,
        locatedCauchyFilterDecode_encode_bhist continuation,
        locatedCauchyFilterDecode_encode_bhist provenance,
        locatedCauchyFilterDecode_encode_bhist localNameCert]

private theorem locatedCauchyFilterToEventFlow_injective
    {x y : LocatedCauchyFilterUp} :
    locatedCauchyFilterToEventFlow x = locatedCauchyFilterToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hxy
  have optionEq : some x = some y := by
    calc
      some x = locatedCauchyFilterFromEventFlow (locatedCauchyFilterToEventFlow x) :=
        (locatedCauchyFilter_round_trip x).symm
      _ = locatedCauchyFilterFromEventFlow (locatedCauchyFilterToEventFlow y) :=
        congrArg locatedCauchyFilterFromEventFlow hxy
      _ = some y := locatedCauchyFilter_round_trip y
  exact Option.some.inj optionEq

private theorem locatedCauchyFilter_fields_faithful :
    ∀ x y : LocatedCauchyFilterUp, locatedCauchyFilterFields x = locatedCauchyFilterFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk filter₁ basis₁ regular₁ stream₁ readback₁ dyadic₁ locatedTail₁ realSeal₁
      transport₁ continuation₁ provenance₁ localNameCert₁ =>
      cases y with
      | mk filter₂ basis₂ regular₂ stream₂ readback₂ dyadic₂ locatedTail₂ realSeal₂
          transport₂ continuation₂ provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance locatedCauchyFilterBHistCarrier : BHistCarrier LocatedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedCauchyFilterToEventFlow
  fromEventFlow := locatedCauchyFilterFromEventFlow

instance locatedCauchyFilterChapterTasteGate : ChapterTasteGate LocatedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedCauchyFilterFromEventFlow (locatedCauchyFilterToEventFlow x) = some x
    exact locatedCauchyFilter_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedCauchyFilterToEventFlow_injective heq)

instance locatedCauchyFilterFieldFaithful : FieldFaithful LocatedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedCauchyFilterFields
  field_faithful := locatedCauchyFilter_fields_faithful

instance locatedCauchyFilterNontrivial :
    BEDC.Meta.TasteGate.Nontrivial LocatedCauchyFilterUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedCauchyFilterUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedCauchyFilterUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedCauchyFilterUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedCauchyFilterChapterTasteGate

theorem LocatedCauchyFilterTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate LocatedCauchyFilterUp) ∧
      Nonempty (FieldFaithful LocatedCauchyFilterUp) ∧
        Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedCauchyFilterUp) ∧
          (∀ h : BHist, locatedCauchyFilterDecodeBHist (locatedCauchyFilterEncodeBHist h) = h) ∧
            (∀ x : LocatedCauchyFilterUp,
              locatedCauchyFilterFromEventFlow (locatedCauchyFilterToEventFlow x) = some x) ∧
              (∀ x y : LocatedCauchyFilterUp,
                locatedCauchyFilterToEventFlow x = locatedCauchyFilterToEventFlow y → x = y) ∧
                locatedCauchyFilterEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨⟨locatedCauchyFilterChapterTasteGate⟩,
      ⟨locatedCauchyFilterFieldFaithful⟩,
      ⟨locatedCauchyFilterNontrivial⟩,
      locatedCauchyFilterDecode_encode_bhist,
      locatedCauchyFilter_round_trip,
      (fun _ _ heq => locatedCauchyFilterToEventFlow_injective heq),
      rfl⟩

end BEDC.Derived.LocatedCauchyFilterUp
