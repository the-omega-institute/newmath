import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicTailRadiusLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicTailRadiusLedgerUp : Type where
  | mk (precision tailWindow streamWindows dyadicReadback regSeqHandoff realSeal
      transport routes provenance localName : BHist) : DyadicTailRadiusLedgerUp
  deriving DecidableEq

def dyadicTailRadiusLedgerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicTailRadiusLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicTailRadiusLedgerEncodeBHist h

def dyadicTailRadiusLedgerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicTailRadiusLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicTailRadiusLedgerDecodeBHist tail)

private theorem dyadicTailRadiusLedgerDecode_encode_bhist :
    ∀ h : BHist,
      dyadicTailRadiusLedgerDecodeBHist
        (dyadicTailRadiusLedgerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem dyadicTailRadiusLedger_mk_congr
    {precision precision' tailWindow tailWindow' streamWindows streamWindows'
      dyadicReadback dyadicReadback' regSeqHandoff regSeqHandoff' realSeal realSeal'
      transport transport' routes routes' provenance provenance' localName localName' : BHist}
    (hPrecision : precision' = precision)
    (hTailWindow : tailWindow' = tailWindow)
    (hStreamWindows : streamWindows' = streamWindows)
    (hDyadicReadback : dyadicReadback' = dyadicReadback)
    (hRegSeqHandoff : regSeqHandoff' = regSeqHandoff)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hLocalName : localName' = localName) :
    DyadicTailRadiusLedgerUp.mk precision' tailWindow' streamWindows' dyadicReadback'
        regSeqHandoff' realSeal' transport' routes' provenance' localName' =
      DyadicTailRadiusLedgerUp.mk precision tailWindow streamWindows dyadicReadback
        regSeqHandoff realSeal transport routes provenance localName := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hPrecision
  cases hTailWindow
  cases hStreamWindows
  cases hDyadicReadback
  cases hRegSeqHandoff
  cases hRealSeal
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hLocalName
  rfl

def dyadicTailRadiusLedgerToEventFlow : DyadicTailRadiusLedgerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicTailRadiusLedgerUp.mk precision tailWindow streamWindows dyadicReadback
      regSeqHandoff realSeal transport routes provenance localName =>
      [[BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist precision,
        [BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist tailWindow,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist streamWindows,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist dyadicReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist regSeqHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        dyadicTailRadiusLedgerEncodeBHist localName]

def dyadicTailRadiusLedgerFromEventFlow :
    EventFlow → Option DyadicTailRadiusLedgerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | precision :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | tailWindow :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | streamWindows :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | dyadicReadback :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | regSeqHandoff :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | realSeal :: rest11 =>
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
                                                              | routes :: rest15 =>
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
                                                                              | localName :: rest19 =>
                                                                                  match rest19 with
                                                                                  | [] =>
                                                                                      some
                                                                                        (DyadicTailRadiusLedgerUp.mk
                                                                                          (dyadicTailRadiusLedgerDecodeBHist precision)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist tailWindow)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist streamWindows)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist dyadicReadback)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist regSeqHandoff)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist realSeal)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist transport)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist routes)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist provenance)
                                                                                          (dyadicTailRadiusLedgerDecodeBHist localName))
                                                                                  | _ :: _ => none

private theorem dyadicTailRadiusLedger_round_trip :
    ∀ x : DyadicTailRadiusLedgerUp,
      dyadicTailRadiusLedgerFromEventFlow
        (dyadicTailRadiusLedgerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk precision tailWindow streamWindows dyadicReadback regSeqHandoff realSeal
      transport routes provenance localName =>
      change
        some
          (DyadicTailRadiusLedgerUp.mk
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist precision))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist tailWindow))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist streamWindows))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist dyadicReadback))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist regSeqHandoff))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist realSeal))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist transport))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist routes))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist provenance))
            (dyadicTailRadiusLedgerDecodeBHist
              (dyadicTailRadiusLedgerEncodeBHist localName))) =
          some
            (DyadicTailRadiusLedgerUp.mk precision tailWindow streamWindows
              dyadicReadback regSeqHandoff realSeal transport routes provenance
              localName)
      exact
        congrArg some
          (dyadicTailRadiusLedger_mk_congr
            (dyadicTailRadiusLedgerDecode_encode_bhist precision)
            (dyadicTailRadiusLedgerDecode_encode_bhist tailWindow)
            (dyadicTailRadiusLedgerDecode_encode_bhist streamWindows)
            (dyadicTailRadiusLedgerDecode_encode_bhist dyadicReadback)
            (dyadicTailRadiusLedgerDecode_encode_bhist regSeqHandoff)
            (dyadicTailRadiusLedgerDecode_encode_bhist realSeal)
            (dyadicTailRadiusLedgerDecode_encode_bhist transport)
            (dyadicTailRadiusLedgerDecode_encode_bhist routes)
            (dyadicTailRadiusLedgerDecode_encode_bhist provenance)
            (dyadicTailRadiusLedgerDecode_encode_bhist localName))

private theorem dyadicTailRadiusLedgerToEventFlow_injective
    {x y : DyadicTailRadiusLedgerUp} :
    dyadicTailRadiusLedgerToEventFlow x =
      dyadicTailRadiusLedgerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicTailRadiusLedgerFromEventFlow
          (dyadicTailRadiusLedgerToEventFlow x) =
        dyadicTailRadiusLedgerFromEventFlow
          (dyadicTailRadiusLedgerToEventFlow y) :=
    congrArg dyadicTailRadiusLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicTailRadiusLedger_round_trip x).symm
      (Eq.trans hread (dyadicTailRadiusLedger_round_trip y)))

instance dyadicTailRadiusLedgerBHistCarrier :
    BHistCarrier DyadicTailRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicTailRadiusLedgerToEventFlow
  fromEventFlow := dyadicTailRadiusLedgerFromEventFlow

instance dyadicTailRadiusLedgerChapterTasteGate :
    ChapterTasteGate DyadicTailRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      dyadicTailRadiusLedgerFromEventFlow
        (dyadicTailRadiusLedgerToEventFlow x) = some x
    exact dyadicTailRadiusLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicTailRadiusLedgerToEventFlow_injective heq)

instance dyadicTailRadiusLedgerFieldFaithful :
    FieldFaithful DyadicTailRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | DyadicTailRadiusLedgerUp.mk precision tailWindow streamWindows dyadicReadback
        regSeqHandoff realSeal transport routes provenance localName =>
        [precision, tailWindow, streamWindows, dyadicReadback, regSeqHandoff, realSeal,
          transport, routes, provenance, localName]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk precision tailWindow streamWindows dyadicReadback regSeqHandoff realSeal
        transport routes provenance localName =>
        cases y with
        | mk precision' tailWindow' streamWindows' dyadicReadback' regSeqHandoff'
            realSeal' transport' routes' provenance' localName' =>
            cases hfields
            rfl

instance dyadicTailRadiusLedgerNontrivial :
    Nontrivial DyadicTailRadiusLedgerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨DyadicTailRadiusLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      DyadicTailRadiusLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate DyadicTailRadiusLedgerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicTailRadiusLedgerChapterTasteGate

theorem DyadicTailRadiusLedgerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      dyadicTailRadiusLedgerDecodeBHist
        (dyadicTailRadiusLedgerEncodeBHist h) = h) ∧
      (∀ x : DyadicTailRadiusLedgerUp,
        dyadicTailRadiusLedgerFromEventFlow
          (dyadicTailRadiusLedgerToEventFlow x) = some x) ∧
        (∀ x y : DyadicTailRadiusLedgerUp,
          dyadicTailRadiusLedgerToEventFlow x =
            dyadicTailRadiusLedgerToEventFlow y → x = y) ∧
          dyadicTailRadiusLedgerEncodeBHist BHist.Empty = ([] : List BMark) ∧
            (∃ x y : DyadicTailRadiusLedgerUp, x ≠ y) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicTailRadiusLedgerDecode_encode_bhist
  · constructor
    · exact dyadicTailRadiusLedger_round_trip
    · constructor
      · intro x y heq
        exact dyadicTailRadiusLedgerToEventFlow_injective heq
      · constructor
        · rfl
        · exact
            ⟨DyadicTailRadiusLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty,
              DyadicTailRadiusLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty,
              by
                intro h
                cases h⟩

end BEDC.Derived.DyadicTailRadiusLedgerUp
