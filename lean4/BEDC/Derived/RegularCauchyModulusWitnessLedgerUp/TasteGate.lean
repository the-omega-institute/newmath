import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RegularCauchyModulusWitnessLedgerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RegularCauchyModulusWitnessLedgerUp : Type where
  | mk :
      (source modulusWitness window normalizer tailBudget dyadic readback sealRow transport route
        provenance name : BHist) →
      RegularCauchyModulusWitnessLedgerUp
  deriving DecidableEq

def regularCauchyModulusWitnessLedgerEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: regularCauchyModulusWitnessLedgerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: regularCauchyModulusWitnessLedgerEncodeBHist h

def regularCauchyModulusWitnessLedgerDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (regularCauchyModulusWitnessLedgerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (regularCauchyModulusWitnessLedgerDecodeBHist tail)

private theorem regularCauchyModulusWitnessLedger_decode_encode_bhist :
    ∀ h : BHist,
      regularCauchyModulusWitnessLedgerDecodeBHist
        (regularCauchyModulusWitnessLedgerEncodeBHist h) = h := by
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem regularCauchyModulusWitnessLedger_mk_congr
    {source source' modulusWitness modulusWitness' window window' normalizer normalizer'
      tailBudget tailBudget' dyadic dyadic' readback readback' sealRow sealRow'
      transport transport' route route' provenance provenance' name name' : BHist}
    (hSource : source' = source)
    (hModulusWitness : modulusWitness' = modulusWitness)
    (hWindow : window' = window)
    (hNormalizer : normalizer' = normalizer)
    (hTailBudget : tailBudget' = tailBudget)
    (hDyadic : dyadic' = dyadic)
    (hReadback : readback' = readback)
    (hSeal : sealRow' = sealRow)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RegularCauchyModulusWitnessLedgerUp.mk source' modulusWitness' window' normalizer'
        tailBudget' dyadic' readback' sealRow' transport' route' provenance' name' =
      RegularCauchyModulusWitnessLedgerUp.mk source modulusWitness window normalizer tailBudget
        dyadic readback sealRow transport route provenance name := by
  cases hSource
  cases hModulusWitness
  cases hWindow
  cases hNormalizer
  cases hTailBudget
  cases hDyadic
  cases hReadback
  cases hSeal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def regularCauchyModulusWitnessLedgerToEventFlow :
    RegularCauchyModulusWitnessLedgerUp → EventFlow
  | RegularCauchyModulusWitnessLedgerUp.mk source modulusWitness window normalizer tailBudget
      dyadic readback sealRow transport route provenance name =>
      [[BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist source,
        [BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist modulusWitness,
        [BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist normalizer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist tailBudget,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist sealRow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        regularCauchyModulusWitnessLedgerEncodeBHist name]

def regularCauchyModulusWitnessLedgerFromEventFlow :
    EventFlow → Option RegularCauchyModulusWitnessLedgerUp
  | [] => none
  | _tag0 :: source :: _tag1 :: modulusWitness :: _tag2 :: window :: _tag3 ::
      normalizer :: _tag4 :: tailBudget :: _tag5 :: dyadic :: _tag6 :: readback ::
      _tag7 :: sealRow :: _tag8 :: transport :: _tag9 :: route :: _tag10 :: provenance ::
      _tag11 :: name :: [] =>
      some
        (RegularCauchyModulusWitnessLedgerUp.mk
          (regularCauchyModulusWitnessLedgerDecodeBHist source)
          (regularCauchyModulusWitnessLedgerDecodeBHist modulusWitness)
          (regularCauchyModulusWitnessLedgerDecodeBHist window)
          (regularCauchyModulusWitnessLedgerDecodeBHist normalizer)
          (regularCauchyModulusWitnessLedgerDecodeBHist tailBudget)
          (regularCauchyModulusWitnessLedgerDecodeBHist dyadic)
          (regularCauchyModulusWitnessLedgerDecodeBHist readback)
          (regularCauchyModulusWitnessLedgerDecodeBHist sealRow)
          (regularCauchyModulusWitnessLedgerDecodeBHist transport)
          (regularCauchyModulusWitnessLedgerDecodeBHist route)
          (regularCauchyModulusWitnessLedgerDecodeBHist provenance)
          (regularCauchyModulusWitnessLedgerDecodeBHist name))
  | _ => none

private theorem regularCauchyModulusWitnessLedger_round_trip :
    ∀ x : RegularCauchyModulusWitnessLedgerUp,
      regularCauchyModulusWitnessLedgerFromEventFlow
        (regularCauchyModulusWitnessLedgerToEventFlow x) = some x := by
  intro x
  cases x with
  | mk source modulusWitness window normalizer tailBudget dyadic readback sealRow transport route
      provenance name =>
      change
        some
          (RegularCauchyModulusWitnessLedgerUp.mk
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist source))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist modulusWitness))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist window))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist normalizer))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist tailBudget))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist dyadic))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist readback))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist sealRow))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist transport))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist route))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist provenance))
            (regularCauchyModulusWitnessLedgerDecodeBHist
              (regularCauchyModulusWitnessLedgerEncodeBHist name))) =
          some
            (RegularCauchyModulusWitnessLedgerUp.mk source modulusWitness window normalizer
              tailBudget dyadic readback sealRow transport route provenance name)
      exact
        congrArg some
          (regularCauchyModulusWitnessLedger_mk_congr
            (regularCauchyModulusWitnessLedger_decode_encode_bhist source)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist modulusWitness)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist window)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist normalizer)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist tailBudget)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist dyadic)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist readback)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist sealRow)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist transport)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist route)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist provenance)
            (regularCauchyModulusWitnessLedger_decode_encode_bhist name))

private theorem regularCauchyModulusWitnessLedgerToEventFlow_injective
    {x y : RegularCauchyModulusWitnessLedgerUp} :
    regularCauchyModulusWitnessLedgerToEventFlow x =
      regularCauchyModulusWitnessLedgerToEventFlow y → x = y := by
  intro heq
  have hread :
      regularCauchyModulusWitnessLedgerFromEventFlow
          (regularCauchyModulusWitnessLedgerToEventFlow x) =
        regularCauchyModulusWitnessLedgerFromEventFlow
          (regularCauchyModulusWitnessLedgerToEventFlow y) :=
    congrArg regularCauchyModulusWitnessLedgerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (regularCauchyModulusWitnessLedger_round_trip x).symm
      (Eq.trans hread (regularCauchyModulusWitnessLedger_round_trip y)))

instance regularCauchyModulusWitnessLedgerBHistCarrier :
    BHistCarrier RegularCauchyModulusWitnessLedgerUp where
  toEventFlow := regularCauchyModulusWitnessLedgerToEventFlow
  fromEventFlow := regularCauchyModulusWitnessLedgerFromEventFlow

instance regularCauchyModulusWitnessLedgerChapterTasteGate :
    ChapterTasteGate RegularCauchyModulusWitnessLedgerUp where
  round_trip := by
    intro x
    change
      regularCauchyModulusWitnessLedgerFromEventFlow
        (regularCauchyModulusWitnessLedgerToEventFlow x) = some x
    exact regularCauchyModulusWitnessLedger_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (regularCauchyModulusWitnessLedgerToEventFlow_injective heq)

instance regularCauchyModulusWitnessLedgerFieldFaithful :
    FieldFaithful RegularCauchyModulusWitnessLedgerUp where
  fields
    | RegularCauchyModulusWitnessLedgerUp.mk source modulusWitness window normalizer tailBudget
        dyadic readback sealRow transport route provenance name =>
        [source, modulusWitness, window, normalizer, tailBudget, dyadic, readback, sealRow,
          transport, route, provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk source modulusWitness window normalizer tailBudget dyadic readback sealRow transport route
        provenance name =>
        cases y with
        | mk source' modulusWitness' window' normalizer' tailBudget' dyadic' readback' sealRow'
            transport' route' provenance' name' =>
            cases hfields
            rfl

instance regularCauchyModulusWitnessLedgerNontrivial :
    Nontrivial RegularCauchyModulusWitnessLedgerUp where
  witness_pair :=
    ⟨RegularCauchyModulusWitnessLedgerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      RegularCauchyModulusWitnessLedgerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RegularCauchyModulusWitnessLedgerUp :=
  inferInstance

end BEDC.Derived.RegularCauchyModulusWitnessLedgerUp
