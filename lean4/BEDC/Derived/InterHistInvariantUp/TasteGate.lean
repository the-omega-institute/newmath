import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.InterHistInvariantUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive InterHistInvariantUp : Type where
  | mk :
      (leftHist rightHist relation invariant observerSymmetry hsameTransport contRoute
        provenance nameCert : BHist) →
      InterHistInvariantUp
  deriving DecidableEq

def interHistInvariantEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: interHistInvariantEncodeBHist h
  | BHist.e1 h => BMark.b1 :: interHistInvariantEncodeBHist h

def interHistInvariantDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (interHistInvariantDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (interHistInvariantDecodeBHist tail)

private theorem interHistInvariantDecode_encode_bhist :
    ∀ h : BHist, interHistInvariantDecodeBHist (interHistInvariantEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def interHistInvariantToEventFlow : InterHistInvariantUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | InterHistInvariantUp.mk leftHist rightHist relation invariant observerSymmetry
      hsameTransport contRoute provenance nameCert =>
      [[BMark.b0],
        interHistInvariantEncodeBHist leftHist,
        [BMark.b1, BMark.b0],
        interHistInvariantEncodeBHist rightHist,
        [BMark.b1, BMark.b1, BMark.b0],
        interHistInvariantEncodeBHist relation,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistInvariantEncodeBHist invariant,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistInvariantEncodeBHist observerSymmetry,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistInvariantEncodeBHist hsameTransport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        interHistInvariantEncodeBHist contRoute,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        interHistInvariantEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        interHistInvariantEncodeBHist nameCert]

def interHistInvariantFromEventFlow : EventFlow → Option InterHistInvariantUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | leftHist :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | rightHist :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | relation :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | invariant :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | observerSymmetry :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | hsameTransport :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | contRoute :: rest13 =>
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
                                                                      | nameCert ::
                                                                          rest17 =>
                                                                          match
                                                                            rest17
                                                                          with
                                                                          | [] =>
                                                                              some
                                                                                (InterHistInvariantUp.mk
                                                                                  (interHistInvariantDecodeBHist
                                                                                    leftHist)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    rightHist)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    relation)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    invariant)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    observerSymmetry)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    hsameTransport)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    contRoute)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    provenance)
                                                                                  (interHistInvariantDecodeBHist
                                                                                    nameCert))
                                                                          | _ :: _ =>
                                                                              none

private theorem interHistInvariant_round_trip :
    ∀ x : InterHistInvariantUp,
      interHistInvariantFromEventFlow (interHistInvariantToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk leftHist rightHist relation invariant observerSymmetry hsameTransport contRoute
      provenance nameCert =>
      change
        some
          (InterHistInvariantUp.mk
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist leftHist))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist rightHist))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist relation))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist invariant))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist observerSymmetry))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist hsameTransport))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist contRoute))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist provenance))
            (interHistInvariantDecodeBHist (interHistInvariantEncodeBHist nameCert))) =
          some
            (InterHistInvariantUp.mk leftHist rightHist relation invariant observerSymmetry
              hsameTransport contRoute provenance nameCert)
      rw [interHistInvariantDecode_encode_bhist leftHist,
        interHistInvariantDecode_encode_bhist rightHist,
        interHistInvariantDecode_encode_bhist relation,
        interHistInvariantDecode_encode_bhist invariant,
        interHistInvariantDecode_encode_bhist observerSymmetry,
        interHistInvariantDecode_encode_bhist hsameTransport,
        interHistInvariantDecode_encode_bhist contRoute,
        interHistInvariantDecode_encode_bhist provenance,
        interHistInvariantDecode_encode_bhist nameCert]

private theorem interHistInvariantToEventFlow_injective {x y : InterHistInvariantUp} :
    interHistInvariantToEventFlow x = interHistInvariantToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      interHistInvariantFromEventFlow (interHistInvariantToEventFlow x) =
        interHistInvariantFromEventFlow (interHistInvariantToEventFlow y) :=
    congrArg interHistInvariantFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (interHistInvariant_round_trip x).symm
      (Eq.trans hread (interHistInvariant_round_trip y)))

instance interHistInvariantBHistCarrier : BHistCarrier InterHistInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := interHistInvariantToEventFlow
  fromEventFlow := interHistInvariantFromEventFlow

instance interHistInvariantChapterTasteGate : ChapterTasteGate InterHistInvariantUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change interHistInvariantFromEventFlow (interHistInvariantToEventFlow x) = some x
    exact interHistInvariant_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (interHistInvariantToEventFlow_injective heq)

def taste_gate : ChapterTasteGate InterHistInvariantUp :=
  interHistInvariantChapterTasteGate

theorem InterHistInvariantTasteGate_single_carrier_alignment :
    (∀ h : BHist, interHistInvariantDecodeBHist (interHistInvariantEncodeBHist h) = h) ∧
      (∀ x : InterHistInvariantUp,
        interHistInvariantFromEventFlow (interHistInvariantToEventFlow x) = some x) ∧
        (∀ x y : InterHistInvariantUp,
          interHistInvariantToEventFlow x = interHistInvariantToEventFlow y → x = y) ∧
          interHistInvariantEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact
    ⟨interHistInvariantDecode_encode_bhist, interHistInvariant_round_trip,
      (fun _x _y heq => interHistInvariantToEventFlow_injective heq), rfl⟩

end BEDC.Derived.InterHistInvariantUp
