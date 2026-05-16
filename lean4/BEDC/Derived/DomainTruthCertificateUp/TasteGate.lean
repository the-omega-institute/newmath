import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DomainTruthCertificateUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DomainTruthCertificateUp : Type where
  | mk :
      (truth domain openFit observerInvariant continuation failure transport replay provenance
        package localName : BHist) →
      DomainTruthCertificateUp
  deriving DecidableEq

def domainTruthCertificateEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: domainTruthCertificateEncodeBHist h
  | BHist.e1 h => BMark.b1 :: domainTruthCertificateEncodeBHist h

def domainTruthCertificateDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (domainTruthCertificateDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (domainTruthCertificateDecodeBHist tail)

private theorem domainTruthCertificateDecode_encode_bhist :
    ∀ h : BHist,
      domainTruthCertificateDecodeBHist (domainTruthCertificateEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def domainTruthCertificateToEventFlow : DomainTruthCertificateUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation failure
      transport replay provenance package localName =>
      [[BMark.b0],
        domainTruthCertificateEncodeBHist truth,
        [BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist domain,
        [BMark.b1, BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist openFit,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist observerInvariant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist continuation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist failure,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        domainTruthCertificateEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist package,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        domainTruthCertificateEncodeBHist localName]

private def domainTruthCertificateDecodePacket
    (truth domain openFit observerInvariant continuation failure transport replay provenance
      package localName : RawEvent) : DomainTruthCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  DomainTruthCertificateUp.mk
    (domainTruthCertificateDecodeBHist truth)
    (domainTruthCertificateDecodeBHist domain)
    (domainTruthCertificateDecodeBHist openFit)
    (domainTruthCertificateDecodeBHist observerInvariant)
    (domainTruthCertificateDecodeBHist continuation)
    (domainTruthCertificateDecodeBHist failure)
    (domainTruthCertificateDecodeBHist transport)
    (domainTruthCertificateDecodeBHist replay)
    (domainTruthCertificateDecodeBHist provenance)
    (domainTruthCertificateDecodeBHist package)
    (domainTruthCertificateDecodeBHist localName)

def domainTruthCertificateFromEventFlow : EventFlow → Option DomainTruthCertificateUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | truth :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | domain :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | openFit :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | observerInvariant :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | continuation :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | failure :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | transport :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | replay :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | provenance :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | package :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] => none
                                                                                  | _tag10 :: rest20 =>
                                                                                      match rest20 with
                                                                                      | [] => none
                                                                                      | localName :: rest21 =>
                                                                                          match rest21 with
                                                                                          | [] =>
                                                                                              some
                                                                                                (domainTruthCertificateDecodePacket
                                                                                                  truth domain openFit
                                                                                                  observerInvariant continuation
                                                                                                  failure transport replay
                                                                                                  provenance package localName)
                                                                                          | _ :: _ => none

private theorem domainTruthCertificate_round_trip :
    ∀ x : DomainTruthCertificateUp,
      domainTruthCertificateFromEventFlow (domainTruthCertificateToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk truth domain openFit observerInvariant continuation failure transport replay provenance
      package localName =>
      change
        some
          (domainTruthCertificateDecodePacket
            (domainTruthCertificateEncodeBHist truth)
            (domainTruthCertificateEncodeBHist domain)
            (domainTruthCertificateEncodeBHist openFit)
            (domainTruthCertificateEncodeBHist observerInvariant)
            (domainTruthCertificateEncodeBHist continuation)
            (domainTruthCertificateEncodeBHist failure)
            (domainTruthCertificateEncodeBHist transport)
            (domainTruthCertificateEncodeBHist replay)
            (domainTruthCertificateEncodeBHist provenance)
            (domainTruthCertificateEncodeBHist package)
            (domainTruthCertificateEncodeBHist localName)) =
          some
            (DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation
              failure transport replay provenance package localName)
      unfold domainTruthCertificateDecodePacket
      rw [domainTruthCertificateDecode_encode_bhist truth,
        domainTruthCertificateDecode_encode_bhist domain,
        domainTruthCertificateDecode_encode_bhist openFit,
        domainTruthCertificateDecode_encode_bhist observerInvariant,
        domainTruthCertificateDecode_encode_bhist continuation,
        domainTruthCertificateDecode_encode_bhist failure,
        domainTruthCertificateDecode_encode_bhist transport,
        domainTruthCertificateDecode_encode_bhist replay,
        domainTruthCertificateDecode_encode_bhist provenance,
        domainTruthCertificateDecode_encode_bhist package,
        domainTruthCertificateDecode_encode_bhist localName]

private theorem domainTruthCertificateToEventFlow_injective
    {x y : DomainTruthCertificateUp} :
    domainTruthCertificateToEventFlow x = domainTruthCertificateToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      domainTruthCertificateFromEventFlow (domainTruthCertificateToEventFlow x) =
        domainTruthCertificateFromEventFlow (domainTruthCertificateToEventFlow y) :=
    congrArg domainTruthCertificateFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (domainTruthCertificate_round_trip x).symm
      (Eq.trans hread (domainTruthCertificate_round_trip y)))

private def domainTruthCertificateFields : DomainTruthCertificateUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | DomainTruthCertificateUp.mk truth domain openFit observerInvariant continuation failure
      transport replay provenance package localName =>
      [truth, domain, openFit, observerInvariant, continuation, failure, transport, replay,
        provenance, package, localName]

private theorem domainTruthCertificate_field_faithful :
    ∀ x y : DomainTruthCertificateUp,
      domainTruthCertificateFields x = domainTruthCertificateFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk truth1 domain1 openFit1 observerInvariant1 continuation1 failure1 transport1 replay1
      provenance1 package1 localName1 =>
      cases y with
      | mk truth2 domain2 openFit2 observerInvariant2 continuation2 failure2 transport2 replay2
          provenance2 package2 localName2 =>
          cases hfields
          rfl

instance domainTruthCertificateBHistCarrier :
    BHistCarrier DomainTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := domainTruthCertificateToEventFlow
  fromEventFlow := domainTruthCertificateFromEventFlow

instance domainTruthCertificateChapterTasteGate :
    ChapterTasteGate DomainTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change domainTruthCertificateFromEventFlow (domainTruthCertificateToEventFlow x) = some x
    exact domainTruthCertificate_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (domainTruthCertificateToEventFlow_injective heq)

instance domainTruthCertificateFieldFaithful :
    FieldFaithful DomainTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := domainTruthCertificateFields
  field_faithful := domainTruthCertificate_field_faithful

instance domainTruthCertificateNontrivial :
    Nontrivial DomainTruthCertificateUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DomainTruthCertificateUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      DomainTruthCertificateUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DomainTruthCertificateUp :=
  -- BEDC touchpoint anchor: BHist BMark
  domainTruthCertificateChapterTasteGate

theorem DomainTruthCertificateTasteGate_single_carrier_alignment :
    (domainTruthCertificateEncodeBHist BHist.Empty = []) ∧
      (∀ h : BHist,
        domainTruthCertificateDecodeBHist (domainTruthCertificateEncodeBHist h) = h) ∧
        (∀ x : DomainTruthCertificateUp,
          domainTruthCertificateFromEventFlow (domainTruthCertificateToEventFlow x) =
            some x) ∧
          (∀ x y : DomainTruthCertificateUp,
            domainTruthCertificateToEventFlow x = domainTruthCertificateToEventFlow y →
              x = y) ∧
            ChapterTasteGate DomainTruthCertificateUp := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨rfl,
      domainTruthCertificateDecode_encode_bhist,
      domainTruthCertificate_round_trip,
      (fun _ _ heq => domainTruthCertificateToEventFlow_injective heq),
      domainTruthCertificateChapterTasteGate⟩

end BEDC.Derived.DomainTruthCertificateUp
