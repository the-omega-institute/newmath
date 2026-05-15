import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICOpenProblemWitnessUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICOpenProblemWitnessUp : Type where
  | mk :
      (subjectReduction confluence normalization decidability typedExamples consistencyFrontier
        transport route provenance name : BHist) → MetaCICOpenProblemWitnessUp
  deriving DecidableEq

def metaCICOpenProblemWitnessEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICOpenProblemWitnessEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICOpenProblemWitnessEncodeBHist h

def metaCICOpenProblemWitnessDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICOpenProblemWitnessDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICOpenProblemWitnessDecodeBHist tail)

private theorem metaCICOpenProblemWitness_decode_encode_bhist :
    ∀ h : BHist,
      metaCICOpenProblemWitnessDecodeBHist
        (metaCICOpenProblemWitnessEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICOpenProblemWitnessFields :
    MetaCICOpenProblemWitnessUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICOpenProblemWitnessUp.mk subjectReduction confluence normalization decidability
      typedExamples consistencyFrontier transport route provenance name =>
      [subjectReduction, confluence, normalization, decidability, typedExamples,
        consistencyFrontier, transport, route, provenance, name]

def metaCICOpenProblemWitnessToEventFlow :
    MetaCICOpenProblemWitnessUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (metaCICOpenProblemWitnessFields x).map metaCICOpenProblemWitnessEncodeBHist

def metaCICOpenProblemWitnessFromEventFlow :
    EventFlow → Option MetaCICOpenProblemWitnessUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _a :: [] => none
  | _a :: _b :: [] => none
  | _a :: _b :: _c :: [] => none
  | _a :: _b :: _c :: _d :: [] => none
  | _a :: _b :: _c :: _d :: _e :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: [] => none
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: [] => none
  | S :: C :: N :: D :: T :: K :: H :: R :: P :: Q :: [] =>
      some
        (MetaCICOpenProblemWitnessUp.mk
          (metaCICOpenProblemWitnessDecodeBHist S)
          (metaCICOpenProblemWitnessDecodeBHist C)
          (metaCICOpenProblemWitnessDecodeBHist N)
          (metaCICOpenProblemWitnessDecodeBHist D)
          (metaCICOpenProblemWitnessDecodeBHist T)
          (metaCICOpenProblemWitnessDecodeBHist K)
          (metaCICOpenProblemWitnessDecodeBHist H)
          (metaCICOpenProblemWitnessDecodeBHist R)
          (metaCICOpenProblemWitnessDecodeBHist P)
          (metaCICOpenProblemWitnessDecodeBHist Q))
  | _a :: _b :: _c :: _d :: _e :: _f :: _g :: _h :: _i :: _j :: _k :: _rest =>
      none

private theorem metaCICOpenProblemWitness_round_trip :
    ∀ x : MetaCICOpenProblemWitnessUp,
      metaCICOpenProblemWitnessFromEventFlow
        (metaCICOpenProblemWitnessToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk subjectReduction confluence normalization decidability typedExamples
      consistencyFrontier transport route provenance name =>
      change
        some
          (MetaCICOpenProblemWitnessUp.mk
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist subjectReduction))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist confluence))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist normalization))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist decidability))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist typedExamples))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist consistencyFrontier))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist transport))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist route))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist provenance))
            (metaCICOpenProblemWitnessDecodeBHist
              (metaCICOpenProblemWitnessEncodeBHist name))) =
          some
            (MetaCICOpenProblemWitnessUp.mk subjectReduction confluence normalization
              decidability typedExamples consistencyFrontier transport route provenance name)
      rw [metaCICOpenProblemWitness_decode_encode_bhist subjectReduction,
        metaCICOpenProblemWitness_decode_encode_bhist confluence,
        metaCICOpenProblemWitness_decode_encode_bhist normalization,
        metaCICOpenProblemWitness_decode_encode_bhist decidability,
        metaCICOpenProblemWitness_decode_encode_bhist typedExamples,
        metaCICOpenProblemWitness_decode_encode_bhist consistencyFrontier,
        metaCICOpenProblemWitness_decode_encode_bhist transport,
        metaCICOpenProblemWitness_decode_encode_bhist route,
        metaCICOpenProblemWitness_decode_encode_bhist provenance,
        metaCICOpenProblemWitness_decode_encode_bhist name]

private theorem metaCICOpenProblemWitnessToEventFlow_injective
    {x y : MetaCICOpenProblemWitnessUp} :
    metaCICOpenProblemWitnessToEventFlow x =
      metaCICOpenProblemWitnessToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICOpenProblemWitnessFromEventFlow
          (metaCICOpenProblemWitnessToEventFlow x) =
        metaCICOpenProblemWitnessFromEventFlow
          (metaCICOpenProblemWitnessToEventFlow y) :=
    congrArg metaCICOpenProblemWitnessFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICOpenProblemWitness_round_trip x).symm
      (Eq.trans hread (metaCICOpenProblemWitness_round_trip y)))

private theorem metaCICOpenProblemWitness_fields_faithful :
    ∀ x y : MetaCICOpenProblemWitnessUp,
      metaCICOpenProblemWitnessFields x = metaCICOpenProblemWitnessFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk subjectReduction confluence normalization decidability typedExamples
      consistencyFrontier transport route provenance name =>
      cases y with
      | mk subjectReduction' confluence' normalization' decidability' typedExamples'
          consistencyFrontier' transport' route' provenance' name' =>
          cases hfields
          rfl

instance metaCICOpenProblemWitnessBHistCarrier :
    BHistCarrier MetaCICOpenProblemWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICOpenProblemWitnessToEventFlow
  fromEventFlow := metaCICOpenProblemWitnessFromEventFlow

instance taste_gate :
    ChapterTasteGate MetaCICOpenProblemWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICOpenProblemWitnessFromEventFlow
        (metaCICOpenProblemWitnessToEventFlow x) = some x
    exact metaCICOpenProblemWitness_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICOpenProblemWitnessToEventFlow_injective heq)

instance metaCICOpenProblemWitnessFieldFaithful :
    FieldFaithful MetaCICOpenProblemWitnessUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := metaCICOpenProblemWitnessFields
  field_faithful := metaCICOpenProblemWitness_fields_faithful

instance metaCICOpenProblemWitnessNontrivial :
    Nontrivial MetaCICOpenProblemWitnessUp where
  witness_pair :=
    ⟨MetaCICOpenProblemWitnessUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICOpenProblemWitnessUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

end BEDC.Derived.MetaCICOpenProblemWitnessUp
