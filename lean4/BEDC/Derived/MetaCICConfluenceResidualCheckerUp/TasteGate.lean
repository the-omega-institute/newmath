import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.MetaCICConfluenceResidualCheckerUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive MetaCICConfluenceResidualCheckerUp : Type where
  | mk (typedWindow redexFrontier boundedChecker localJoin obstruction checkerStatus
      transport replay provenance localName : BHist) :
      MetaCICConfluenceResidualCheckerUp
  deriving DecidableEq

def metaCICConfluenceResidualCheckerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: metaCICConfluenceResidualCheckerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: metaCICConfluenceResidualCheckerEncodeBHist h

def metaCICConfluenceResidualCheckerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (metaCICConfluenceResidualCheckerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (metaCICConfluenceResidualCheckerDecodeBHist tail)

private theorem metaCICConfluenceResidualCheckerDecode_encode_bhist :
    ∀ h : BHist,
      metaCICConfluenceResidualCheckerDecodeBHist
        (metaCICConfluenceResidualCheckerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def metaCICConfluenceResidualCheckerToEventFlow :
    MetaCICConfluenceResidualCheckerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | MetaCICConfluenceResidualCheckerUp.mk typedWindow redexFrontier boundedChecker
      localJoin obstruction checkerStatus transport replay provenance localName =>
      [[BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist typedWindow,
        [BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist redexFrontier,
        [BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist boundedChecker,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist localJoin,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist obstruction,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist checkerStatus,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        metaCICConfluenceResidualCheckerEncodeBHist localName]

def metaCICConfluenceResidualCheckerFromEventFlow :
    EventFlow → Option MetaCICConfluenceResidualCheckerUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | typedWindow :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | redexFrontier :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | boundedChecker :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | localJoin :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | obstruction :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | checkerStatus :: rest11 =>
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
                                                                              | localName ::
                                                                                  rest19 =>
                                                                                  match rest19
                                                                                  with
                                                                                  | [] =>
                                                                                      some
                                                                                        (MetaCICConfluenceResidualCheckerUp.mk
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            typedWindow)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            redexFrontier)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            boundedChecker)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            localJoin)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            obstruction)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            checkerStatus)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            transport)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            replay)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            provenance)
                                                                                          (metaCICConfluenceResidualCheckerDecodeBHist
                                                                                            localName))
                                                                                  | _ :: _ =>
                                                                                      none

private theorem metaCICConfluenceResidualChecker_round_trip :
    ∀ x : MetaCICConfluenceResidualCheckerUp,
      metaCICConfluenceResidualCheckerFromEventFlow
        (metaCICConfluenceResidualCheckerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk typedWindow redexFrontier boundedChecker localJoin obstruction checkerStatus transport
      replay provenance localName =>
      change
        some
          (MetaCICConfluenceResidualCheckerUp.mk
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist typedWindow))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist redexFrontier))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist boundedChecker))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist localJoin))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist obstruction))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist checkerStatus))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist transport))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist replay))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist provenance))
            (metaCICConfluenceResidualCheckerDecodeBHist
              (metaCICConfluenceResidualCheckerEncodeBHist localName))) =
          some
            (MetaCICConfluenceResidualCheckerUp.mk typedWindow redexFrontier boundedChecker
              localJoin obstruction checkerStatus transport replay provenance localName)
      rw [metaCICConfluenceResidualCheckerDecode_encode_bhist typedWindow,
        metaCICConfluenceResidualCheckerDecode_encode_bhist redexFrontier,
        metaCICConfluenceResidualCheckerDecode_encode_bhist boundedChecker,
        metaCICConfluenceResidualCheckerDecode_encode_bhist localJoin,
        metaCICConfluenceResidualCheckerDecode_encode_bhist obstruction,
        metaCICConfluenceResidualCheckerDecode_encode_bhist checkerStatus,
        metaCICConfluenceResidualCheckerDecode_encode_bhist transport,
        metaCICConfluenceResidualCheckerDecode_encode_bhist replay,
        metaCICConfluenceResidualCheckerDecode_encode_bhist provenance,
        metaCICConfluenceResidualCheckerDecode_encode_bhist localName]

private theorem metaCICConfluenceResidualCheckerToEventFlow_injective
    {x y : MetaCICConfluenceResidualCheckerUp} :
    metaCICConfluenceResidualCheckerToEventFlow x =
      metaCICConfluenceResidualCheckerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      metaCICConfluenceResidualCheckerFromEventFlow
          (metaCICConfluenceResidualCheckerToEventFlow x) =
        metaCICConfluenceResidualCheckerFromEventFlow
          (metaCICConfluenceResidualCheckerToEventFlow y) :=
    congrArg metaCICConfluenceResidualCheckerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (metaCICConfluenceResidualChecker_round_trip x).symm
      (Eq.trans hread (metaCICConfluenceResidualChecker_round_trip y)))

instance metaCICConfluenceResidualCheckerBHistCarrier :
    BHistCarrier MetaCICConfluenceResidualCheckerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := metaCICConfluenceResidualCheckerToEventFlow
  fromEventFlow := metaCICConfluenceResidualCheckerFromEventFlow

instance metaCICConfluenceResidualCheckerChapterTasteGate :
    ChapterTasteGate MetaCICConfluenceResidualCheckerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      metaCICConfluenceResidualCheckerFromEventFlow
        (metaCICConfluenceResidualCheckerToEventFlow x) = some x
    exact metaCICConfluenceResidualChecker_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (metaCICConfluenceResidualCheckerToEventFlow_injective heq)

instance metaCICConfluenceResidualCheckerFieldFaithful :
    FieldFaithful MetaCICConfluenceResidualCheckerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | MetaCICConfluenceResidualCheckerUp.mk typedWindow redexFrontier boundedChecker
        localJoin obstruction checkerStatus transport replay provenance localName =>
        [typedWindow, redexFrontier, boundedChecker, localJoin, obstruction, checkerStatus,
          transport, replay, provenance, localName]
  field_faithful := by
    intro x y h
    cases x with
    | mk typedWindow₁ redexFrontier₁ boundedChecker₁ localJoin₁ obstruction₁ checkerStatus₁
        transport₁ replay₁ provenance₁ localName₁ =>
        cases y with
        | mk typedWindow₂ redexFrontier₂ boundedChecker₂ localJoin₂ obstruction₂
            checkerStatus₂ transport₂ replay₂ provenance₂ localName₂ =>
            injection h with hTypedWindow t1
            injection t1 with hRedexFrontier t2
            injection t2 with hBoundedChecker t3
            injection t3 with hLocalJoin t4
            injection t4 with hObstruction t5
            injection t5 with hCheckerStatus t6
            injection t6 with hTransport t7
            injection t7 with hReplay t8
            injection t8 with hProvenance t9
            injection t9 with hLocalName _
            cases hTypedWindow
            cases hRedexFrontier
            cases hBoundedChecker
            cases hLocalJoin
            cases hObstruction
            cases hCheckerStatus
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hLocalName
            rfl

instance metaCICConfluenceResidualCheckerNontrivial :
    Nontrivial MetaCICConfluenceResidualCheckerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨MetaCICConfluenceResidualCheckerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      MetaCICConfluenceResidualCheckerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate MetaCICConfluenceResidualCheckerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  metaCICConfluenceResidualCheckerChapterTasteGate

theorem MetaCICConfluenceResidualCheckerTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      metaCICConfluenceResidualCheckerDecodeBHist
        (metaCICConfluenceResidualCheckerEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier MetaCICConfluenceResidualCheckerUp) ∧
        Nonempty (ChapterTasteGate MetaCICConfluenceResidualCheckerUp) ∧
          metaCICConfluenceResidualCheckerEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨metaCICConfluenceResidualCheckerDecode_encode_bhist,
      ⟨metaCICConfluenceResidualCheckerBHistCarrier⟩,
      ⟨metaCICConfluenceResidualCheckerChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.MetaCICConfluenceResidualCheckerUp
