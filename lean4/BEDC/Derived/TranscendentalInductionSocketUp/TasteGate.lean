import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Gap
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

/-!
# TranscendentalInductionSocketUp TasteGate carrier.
-/

namespace BEDC.Derived.TranscendentalInductionSocketUp

open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Gap
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

/-- Finite socket packet carrying the displayed induction-boundary rows. -/
inductive TranscendentalInductionSocketUp : Type where
  | mk :
      (source trace request gap handoff transports routes provenance nameCert : BHist) →
      TranscendentalInductionSocketUp
  deriving DecidableEq

def transcendentalInductionSocketEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: transcendentalInductionSocketEncodeBHist h
  | BHist.e1 h => BMark.b1 :: transcendentalInductionSocketEncodeBHist h

def transcendentalInductionSocketDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (transcendentalInductionSocketDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (transcendentalInductionSocketDecodeBHist tail)

private theorem transcendentalInductionSocket_decode_encode_bhist :
    ∀ h : BHist,
      transcendentalInductionSocketDecodeBHist
          (transcendentalInductionSocketEncodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem transcendentalInductionSocket_mk_congr
    {source source' trace trace' request request' gap gap' handoff handoff' transports
      transports' routes routes' provenance provenance' nameCert nameCert' : BHist} :
    source = source' →
      trace = trace' →
        request = request' →
          gap = gap' →
            handoff = handoff' →
              transports = transports' →
                routes = routes' →
                  provenance = provenance' →
                    nameCert = nameCert' →
                      TranscendentalInductionSocketUp.mk source trace request gap handoff
                          transports routes provenance nameCert =
                        TranscendentalInductionSocketUp.mk source' trace' request' gap'
                          handoff' transports' routes' provenance' nameCert' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hsource htrace hrequest hgap hhandoff htransports hroutes hprovenance hnameCert
  cases hsource
  cases htrace
  cases hrequest
  cases hgap
  cases hhandoff
  cases htransports
  cases hroutes
  cases hprovenance
  cases hnameCert
  rfl

def transcendentalInductionSocketToEventFlow :
    TranscendentalInductionSocketUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | TranscendentalInductionSocketUp.mk source trace request gap handoff transports routes
      provenance nameCert =>
      [[BMark.b0],
        transcendentalInductionSocketEncodeBHist source,
        [BMark.b1, BMark.b0],
        transcendentalInductionSocketEncodeBHist trace,
        [BMark.b1, BMark.b1, BMark.b0],
        transcendentalInductionSocketEncodeBHist request,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalInductionSocketEncodeBHist gap,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalInductionSocketEncodeBHist handoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalInductionSocketEncodeBHist transports,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        transcendentalInductionSocketEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        transcendentalInductionSocketEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        transcendentalInductionSocketEncodeBHist nameCert]

def transcendentalInductionSocketFromEventFlow :
    EventFlow → Option TranscendentalInductionSocketUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | source :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | trace :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | request :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | gap :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | handoff :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | transports :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | routes :: rest13 =>
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
                                                                                (TranscendentalInductionSocketUp.mk
                                                                                  (transcendentalInductionSocketDecodeBHist source)
                                                                                  (transcendentalInductionSocketDecodeBHist trace)
                                                                                  (transcendentalInductionSocketDecodeBHist request)
                                                                                  (transcendentalInductionSocketDecodeBHist gap)
                                                                                  (transcendentalInductionSocketDecodeBHist handoff)
                                                                                  (transcendentalInductionSocketDecodeBHist transports)
                                                                                  (transcendentalInductionSocketDecodeBHist routes)
                                                                                  (transcendentalInductionSocketDecodeBHist provenance)
                                                                                  (transcendentalInductionSocketDecodeBHist nameCert))
                                                                          | _ :: _ => none

private theorem transcendentalInductionSocket_round_trip :
    ∀ x : TranscendentalInductionSocketUp,
      transcendentalInductionSocketFromEventFlow
          (transcendentalInductionSocketToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source trace request gap handoff transports routes provenance nameCert =>
      change
        some
            (TranscendentalInductionSocketUp.mk
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist source))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist trace))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist request))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist gap))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist handoff))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist transports))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist routes))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist provenance))
              (transcendentalInductionSocketDecodeBHist
                (transcendentalInductionSocketEncodeBHist nameCert))) =
          some
            (TranscendentalInductionSocketUp.mk source trace request gap handoff transports
              routes provenance nameCert)
      exact congrArg some
        (transcendentalInductionSocket_mk_congr
          (transcendentalInductionSocket_decode_encode_bhist source)
          (transcendentalInductionSocket_decode_encode_bhist trace)
          (transcendentalInductionSocket_decode_encode_bhist request)
          (transcendentalInductionSocket_decode_encode_bhist gap)
          (transcendentalInductionSocket_decode_encode_bhist handoff)
          (transcendentalInductionSocket_decode_encode_bhist transports)
          (transcendentalInductionSocket_decode_encode_bhist routes)
          (transcendentalInductionSocket_decode_encode_bhist provenance)
          (transcendentalInductionSocket_decode_encode_bhist nameCert))

private theorem transcendentalInductionSocketToEventFlow_injective
    {x y : TranscendentalInductionSocketUp} :
    transcendentalInductionSocketToEventFlow x =
      transcendentalInductionSocketToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      transcendentalInductionSocketFromEventFlow
          (transcendentalInductionSocketToEventFlow x) =
        transcendentalInductionSocketFromEventFlow
          (transcendentalInductionSocketToEventFlow y) :=
    congrArg transcendentalInductionSocketFromEventFlow heq
  have someSame :
      some x = some y :=
    Eq.trans (transcendentalInductionSocket_round_trip x).symm
      (Eq.trans hread (transcendentalInductionSocket_round_trip y))
  cases someSame
  rfl

instance transcendentalInductionSocketBHistCarrier :
    BHistCarrier TranscendentalInductionSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := transcendentalInductionSocketToEventFlow
  fromEventFlow := transcendentalInductionSocketFromEventFlow

instance transcendentalInductionSocketChapterTasteGate :
    ChapterTasteGate TranscendentalInductionSocketUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      transcendentalInductionSocketFromEventFlow
          (transcendentalInductionSocketToEventFlow x) =
        some x
    exact transcendentalInductionSocket_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (transcendentalInductionSocketToEventFlow_injective heq)

def taste_gate : ChapterTasteGate TranscendentalInductionSocketUp :=
  -- BEDC touchpoint anchor: BHist BMark
  transcendentalInductionSocketChapterTasteGate

theorem TranscendentalInductionSocketTasteGate_single_carrier_alignment :
    (forall h : BHist,
      transcendentalInductionSocketDecodeBHist
          (transcendentalInductionSocketEncodeBHist h) =
        h) /\
      (forall x : TranscendentalInductionSocketUp,
        transcendentalInductionSocketFromEventFlow
            (transcendentalInductionSocketToEventFlow x) =
          some x) /\
        (forall x y : TranscendentalInductionSocketUp,
          transcendentalInductionSocketToEventFlow x =
            transcendentalInductionSocketToEventFlow y ->
            x = y) /\
          transcendentalInductionSocketEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨transcendentalInductionSocket_decode_encode_bhist,
      transcendentalInductionSocket_round_trip,
      (fun _x _y sameFlow => transcendentalInductionSocketToEventFlow_injective sameFlow),
      rfl⟩

end BEDC.Derived.TranscendentalInductionSocketUp
