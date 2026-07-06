import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.AsymptoticRegularityUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive AsymptoticRegularityUp : Type where
  | mk
      (orbit displacement modulus sealRow stability transport handoff replay provenance
        nameCert : BHist) :
      AsymptoticRegularityUp
  deriving DecidableEq

def asymptoticRegularityEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: asymptoticRegularityEncodeBHist h
  | BHist.e1 h => BMark.b1 :: asymptoticRegularityEncodeBHist h

def asymptoticRegularityDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (asymptoticRegularityDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (asymptoticRegularityDecodeBHist tail)

private theorem asymptoticRegularity_decode_encode_bhist :
    ∀ h : BHist,
      asymptoticRegularityDecodeBHist (asymptoticRegularityEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def asymptoticRegularityFields : AsymptoticRegularityUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | AsymptoticRegularityUp.mk orbit displacement modulus sealRow stability transport handoff
      replay provenance nameCert =>
      [orbit, displacement, modulus, sealRow, stability, transport, handoff, replay,
        provenance, nameCert]

def asymptoticRegularityToEventFlow : AsymptoticRegularityUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (asymptoticRegularityFields x).map asymptoticRegularityEncodeBHist

private def asymptoticRegularityEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => asymptoticRegularityEventAt index rest

def asymptoticRegularityFromEventFlow (ef : EventFlow) : Option AsymptoticRegularityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (AsymptoticRegularityUp.mk
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 0 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 1 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 2 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 3 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 4 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 5 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 6 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 7 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 8 ef))
      (asymptoticRegularityDecodeBHist (asymptoticRegularityEventAt 9 ef)))

private theorem asymptoticRegularity_round_trip :
    ∀ x : AsymptoticRegularityUp,
      asymptoticRegularityFromEventFlow (asymptoticRegularityToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk orbit displacement modulus sealRow stability transport handoff replay provenance
      nameCert =>
      change
        some
            (AsymptoticRegularityUp.mk
              (asymptoticRegularityDecodeBHist (asymptoticRegularityEncodeBHist orbit))
              (asymptoticRegularityDecodeBHist
                (asymptoticRegularityEncodeBHist displacement))
              (asymptoticRegularityDecodeBHist (asymptoticRegularityEncodeBHist modulus))
              (asymptoticRegularityDecodeBHist (asymptoticRegularityEncodeBHist sealRow))
              (asymptoticRegularityDecodeBHist (asymptoticRegularityEncodeBHist stability))
              (asymptoticRegularityDecodeBHist
                (asymptoticRegularityEncodeBHist transport))
              (asymptoticRegularityDecodeBHist (asymptoticRegularityEncodeBHist handoff))
              (asymptoticRegularityDecodeBHist (asymptoticRegularityEncodeBHist replay))
              (asymptoticRegularityDecodeBHist
                (asymptoticRegularityEncodeBHist provenance))
              (asymptoticRegularityDecodeBHist
                (asymptoticRegularityEncodeBHist nameCert))) =
          some
            (AsymptoticRegularityUp.mk orbit displacement modulus sealRow stability transport
              handoff replay provenance nameCert)
      rw [asymptoticRegularity_decode_encode_bhist orbit,
        asymptoticRegularity_decode_encode_bhist displacement,
        asymptoticRegularity_decode_encode_bhist modulus,
        asymptoticRegularity_decode_encode_bhist sealRow,
        asymptoticRegularity_decode_encode_bhist stability,
        asymptoticRegularity_decode_encode_bhist transport,
        asymptoticRegularity_decode_encode_bhist handoff,
        asymptoticRegularity_decode_encode_bhist replay,
        asymptoticRegularity_decode_encode_bhist provenance,
        asymptoticRegularity_decode_encode_bhist nameCert]

private theorem asymptoticRegularityToEventFlow_injective
    {x y : AsymptoticRegularityUp} :
    asymptoticRegularityToEventFlow x = asymptoticRegularityToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      asymptoticRegularityFromEventFlow (asymptoticRegularityToEventFlow x) =
        asymptoticRegularityFromEventFlow (asymptoticRegularityToEventFlow y) :=
    congrArg asymptoticRegularityFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (asymptoticRegularity_round_trip x).symm
      (Eq.trans hread (asymptoticRegularity_round_trip y)))

private theorem asymptoticRegularity_field_faithful :
    ∀ x y : AsymptoticRegularityUp,
      asymptoticRegularityFields x = asymptoticRegularityFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk orbit displacement modulus sealRow stability transport handoff replay provenance
      nameCert =>
      cases y with
      | mk orbit' displacement' modulus' sealRow' stability' transport' handoff' replay'
          provenance' nameCert' =>
          cases hfields
          rfl

instance asymptoticRegularityBHistCarrier : BHistCarrier AsymptoticRegularityUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := asymptoticRegularityToEventFlow
  fromEventFlow := asymptoticRegularityFromEventFlow

instance asymptoticRegularityChapterTasteGate :
    ChapterTasteGate AsymptoticRegularityUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change asymptoticRegularityFromEventFlow (asymptoticRegularityToEventFlow x) = some x
    exact asymptoticRegularity_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (asymptoticRegularityToEventFlow_injective heq)

instance asymptoticRegularityFieldFaithful :
    FieldFaithful AsymptoticRegularityUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := asymptoticRegularityFields
  field_faithful := asymptoticRegularity_field_faithful

instance asymptoticRegularityNontrivial :
    BEDC.Meta.TasteGate.Nontrivial AsymptoticRegularityUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨AsymptoticRegularityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      AsymptoticRegularityUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate AsymptoticRegularityUp :=
  -- BEDC touchpoint anchor: BHist BMark
  asymptoticRegularityChapterTasteGate

theorem AsymptoticRegularityCarrier_namecert_obligations
    (x : AsymptoticRegularityUp) :
    asymptoticRegularityFromEventFlow (asymptoticRegularityToEventFlow x) = some x ∧
      ∃ orbit displacement modulus sealRow stability transport handoff replay provenance
          nameCert : BHist,
        x =
            AsymptoticRegularityUp.mk orbit displacement modulus sealRow stability transport
              handoff replay provenance nameCert ∧
          asymptoticRegularityFields x =
            [orbit, displacement, modulus, sealRow, stability, transport, handoff, replay,
              provenance, nameCert] ∧
            asymptoticRegularityFromEventFlow
                (asymptoticRegularityToEventFlow
                  (AsymptoticRegularityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
              some
                (AsymptoticRegularityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                  BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk orbit displacement modulus sealRow stability transport handoff replay provenance
      nameCert =>
      constructor
      · change
          asymptoticRegularityFromEventFlow
              (asymptoticRegularityToEventFlow
                (AsymptoticRegularityUp.mk orbit displacement modulus sealRow stability
                  transport handoff replay provenance nameCert)) =
            some
              (AsymptoticRegularityUp.mk orbit displacement modulus sealRow stability transport
                handoff replay provenance nameCert)
        exact
          asymptoticRegularity_round_trip
            (AsymptoticRegularityUp.mk orbit displacement modulus sealRow stability transport
              handoff replay provenance nameCert)
      · exact
          ⟨orbit, displacement, modulus, sealRow, stability, transport, handoff, replay,
            provenance, nameCert, rfl, rfl,
            by
              change
                asymptoticRegularityFromEventFlow
                    (asymptoticRegularityToEventFlow
                      (AsymptoticRegularityUp.mk BHist.Empty BHist.Empty BHist.Empty
                        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                        BHist.Empty BHist.Empty)) =
                  some
                    (AsymptoticRegularityUp.mk BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                      BHist.Empty)
              exact
                asymptoticRegularity_round_trip
                  (AsymptoticRegularityUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                    BHist.Empty)⟩

end BEDC.Derived.AsymptoticRegularityUp
