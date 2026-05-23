import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.DyadicBisectionUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive DyadicBisectionUp : Type where
  | mk :
      (initial precision midpoint branch nested endpoint regseq stream real transport route
        name : BHist) →
      DyadicBisectionUp
  deriving DecidableEq

def dyadicBisectionEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: dyadicBisectionEncodeBHist h
  | BHist.e1 h => BMark.b1 :: dyadicBisectionEncodeBHist h

def dyadicBisectionDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (dyadicBisectionDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (dyadicBisectionDecodeBHist tail)

private theorem dyadicBisectionDecode_encode_bhist :
    ∀ h : BHist, dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def dyadicBisectionToEventFlow : DyadicBisectionUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | DyadicBisectionUp.mk initial precision midpoint branch nested endpoint regseq stream real
      transport route name =>
      [[BMark.b0],
        dyadicBisectionEncodeBHist initial,
        [BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist precision,
        [BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist midpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist branch,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist nested,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist endpoint,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist regseq,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        dyadicBisectionEncodeBHist stream,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist real,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        dyadicBisectionEncodeBHist name]

def dyadicBisectionFromEventFlow (ef : EventFlow) : Option DyadicBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | initial :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | precision :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | midpoint :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | branch :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | nested :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | endpoint :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | regseq :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | stream :: rest15 =>
                                                                  match rest15 with
                                                                  | [] => none
                                                                  | _tag8 :: rest16 =>
                                                                      match rest16 with
                                                                      | [] => none
                                                                      | real :: rest17 =>
                                                                          match rest17 with
                                                                          | [] => none
                                                                          | _tag9 :: rest18 =>
                                                                              match rest18 with
                                                                              | [] => none
                                                                              | transport ::
                                                                                  rest19 =>
                                                                                  match
                                                                                    rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      none
                                                                                  | _tag10 ::
                                                                                      rest20 =>
                                                                                      match
                                                                                        rest20
                                                                                      with
                                                                                      | [] =>
                                                                                          none
                                                                                      | route ::
                                                                                          rest21 =>
                                                                                          match
                                                                                            rest21
                                                                                          with
                                                                                          | [] =>
                                                                                              none
                                                                                          | _tag11 ::
                                                                                              rest22 =>
                                                                                              match
                                                                                                rest22
                                                                                              with
                                                                                              | [] =>
                                                                                                  none
                                                                                              | name ::
                                                                                                  rest23 =>
                                                                                                  match
                                                                                                    rest23
                                                                                                  with
                                                                                                  | [] =>
                                                                                                      some
                                                                                                        (DyadicBisectionUp.mk
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            initial)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            precision)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            midpoint)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            branch)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            nested)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            endpoint)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            regseq)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            stream)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            real)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            transport)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            route)
                                                                                                          (dyadicBisectionDecodeBHist
                                                                                                            name))
                                                                                                  | _ :: _ =>
                                                                                                      none

private theorem DyadicBisectionTasteGate_single_carrier_alignment_mk_congr
    {initial initial' precision precision' midpoint midpoint' branch branch' nested nested'
      endpoint endpoint' regseq regseq' stream stream' real real' transport transport'
      route route' name name' : BHist} :
    initial = initial' →
      precision = precision' →
        midpoint = midpoint' →
          branch = branch' →
            nested = nested' →
              endpoint = endpoint' →
                regseq = regseq' →
                  stream = stream' →
                    real = real' →
                      transport = transport' →
                        route = route' →
                          name = name' →
                            DyadicBisectionUp.mk initial precision midpoint branch nested endpoint
                                regseq stream real transport route name =
                              DyadicBisectionUp.mk initial' precision' midpoint' branch' nested'
                                endpoint' regseq' stream' real' transport' route' name' := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hInitial hPrecision hMidpoint hBranch hNested hEndpoint hRegseq hStream hReal
    hTransport hRoute hName
  cases hInitial
  cases hPrecision
  cases hMidpoint
  cases hBranch
  cases hNested
  cases hEndpoint
  cases hRegseq
  cases hStream
  cases hReal
  cases hTransport
  cases hRoute
  cases hName
  rfl

private theorem dyadicBisection_round_trip :
    ∀ x : DyadicBisectionUp,
      dyadicBisectionFromEventFlow (dyadicBisectionToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk initial precision midpoint branch nested endpoint regseq stream real transport route name =>
      change
        some
          (DyadicBisectionUp.mk
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist initial))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist precision))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist midpoint))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist branch))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist nested))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist endpoint))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist regseq))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist stream))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist real))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist transport))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist route))
            (dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist name))) =
          some
            (DyadicBisectionUp.mk initial precision midpoint branch nested endpoint regseq
              stream real transport route name)
      have hInitial := dyadicBisectionDecode_encode_bhist initial
      have hPrecision := dyadicBisectionDecode_encode_bhist precision
      have hMidpoint := dyadicBisectionDecode_encode_bhist midpoint
      have hBranch := dyadicBisectionDecode_encode_bhist branch
      have hNested := dyadicBisectionDecode_encode_bhist nested
      have hEndpoint := dyadicBisectionDecode_encode_bhist endpoint
      have hRegseq := dyadicBisectionDecode_encode_bhist regseq
      have hStream := dyadicBisectionDecode_encode_bhist stream
      have hReal := dyadicBisectionDecode_encode_bhist real
      have hTransport := dyadicBisectionDecode_encode_bhist transport
      have hRoute := dyadicBisectionDecode_encode_bhist route
      have hName := dyadicBisectionDecode_encode_bhist name
      exact congrArg some
        (DyadicBisectionTasteGate_single_carrier_alignment_mk_congr hInitial hPrecision
          hMidpoint hBranch hNested hEndpoint hRegseq hStream hReal hTransport hRoute hName)

private theorem dyadicBisectionToEventFlow_injective {x y : DyadicBisectionUp} :
    dyadicBisectionToEventFlow x = dyadicBisectionToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      dyadicBisectionFromEventFlow (dyadicBisectionToEventFlow x) =
        dyadicBisectionFromEventFlow (dyadicBisectionToEventFlow y) :=
    congrArg dyadicBisectionFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (dyadicBisection_round_trip x).symm
      (Eq.trans hread (dyadicBisection_round_trip y)))

instance dyadicBisectionBHistCarrier : BHistCarrier DyadicBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := dyadicBisectionToEventFlow
  fromEventFlow := dyadicBisectionFromEventFlow

instance dyadicBisectionChapterTasteGate : ChapterTasteGate DyadicBisectionUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change dyadicBisectionFromEventFlow (dyadicBisectionToEventFlow x) = some x
    exact dyadicBisection_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (dyadicBisectionToEventFlow_injective heq)

def taste_gate : ChapterTasteGate DyadicBisectionUp :=
  -- BEDC touchpoint anchor: BHist BMark
  dyadicBisectionChapterTasteGate

theorem DyadicBisectionTasteGate_single_carrier_alignment :
    (∀ h : BHist, dyadicBisectionDecodeBHist (dyadicBisectionEncodeBHist h) = h) ∧
      (∀ x : DyadicBisectionUp,
        dyadicBisectionFromEventFlow (dyadicBisectionToEventFlow x) = some x) ∧
        (∀ x y : DyadicBisectionUp,
          dyadicBisectionToEventFlow x = dyadicBisectionToEventFlow y → x = y) ∧
          dyadicBisectionEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact dyadicBisectionDecode_encode_bhist
  · constructor
    · exact dyadicBisection_round_trip
    · constructor
      · intro x y heq
        exact dyadicBisectionToEventFlow_injective heq
      · rfl

end BEDC.Derived.DyadicBisectionUp
