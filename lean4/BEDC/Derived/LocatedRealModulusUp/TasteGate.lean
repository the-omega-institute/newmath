import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LocatedRealModulusUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LocatedRealModulusUp : Type where
  | mk
      (located precisionLedger streamWindow readback realSeal transport replay provenance
        name : BHist) :
      LocatedRealModulusUp
  deriving DecidableEq

def locatedRealModulusEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: locatedRealModulusEncodeBHist h
  | BHist.e1 h => BMark.b1 :: locatedRealModulusEncodeBHist h

def locatedRealModulusDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (locatedRealModulusDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (locatedRealModulusDecodeBHist tail)

private theorem locatedRealModulus_decode_encode_bhist :
    ∀ h : BHist, locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def locatedRealModulusFields : LocatedRealModulusUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LocatedRealModulusUp.mk located precisionLedger streamWindow readback realSeal transport
      replay provenance name =>
      [located, precisionLedger, streamWindow, readback, realSeal, transport, replay,
        provenance, name]

def locatedRealModulusToEventFlow : LocatedRealModulusUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (locatedRealModulusFields x).map locatedRealModulusEncodeBHist

def locatedRealModulusFromEventFlow : EventFlow → Option LocatedRealModulusUp := fun flow =>
  -- BEDC touchpoint anchor: BHist BMark
  match flow with
  | [] => none
  | located :: rest0 =>
      match rest0 with
      | [] => none
      | precisionLedger :: rest1 =>
          match rest1 with
          | [] => none
          | streamWindow :: rest2 =>
              match rest2 with
              | [] => none
              | readback :: rest3 =>
                  match rest3 with
                  | [] => none
                  | realSeal :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | replay :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (LocatedRealModulusUp.mk
                                              (locatedRealModulusDecodeBHist located)
                                              (locatedRealModulusDecodeBHist precisionLedger)
                                              (locatedRealModulusDecodeBHist streamWindow)
                                              (locatedRealModulusDecodeBHist readback)
                                              (locatedRealModulusDecodeBHist realSeal)
                                              (locatedRealModulusDecodeBHist transport)
                                              (locatedRealModulusDecodeBHist replay)
                                              (locatedRealModulusDecodeBHist provenance)
                                              (locatedRealModulusDecodeBHist name))
                                      | _ :: _ => none

private theorem locatedRealModulus_round_trip :
    ∀ x : LocatedRealModulusUp,
      locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk located precisionLedger streamWindow readback realSeal transport replay provenance name =>
      change
        some
            (LocatedRealModulusUp.mk
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist located))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist precisionLedger))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist streamWindow))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist readback))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist realSeal))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist transport))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist replay))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist provenance))
              (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist name))) =
          some
            (LocatedRealModulusUp.mk located precisionLedger streamWindow readback realSeal
              transport replay provenance name)
      rw [locatedRealModulus_decode_encode_bhist located]
      rw [locatedRealModulus_decode_encode_bhist precisionLedger]
      rw [locatedRealModulus_decode_encode_bhist streamWindow]
      rw [locatedRealModulus_decode_encode_bhist readback]
      rw [locatedRealModulus_decode_encode_bhist realSeal]
      rw [locatedRealModulus_decode_encode_bhist transport]
      rw [locatedRealModulus_decode_encode_bhist replay]
      rw [locatedRealModulus_decode_encode_bhist provenance]
      rw [locatedRealModulus_decode_encode_bhist name]

private theorem locatedRealModulusToEventFlow_injective {x y : LocatedRealModulusUp} :
    locatedRealModulusToEventFlow x = locatedRealModulusToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) =
        locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow y) :=
    congrArg locatedRealModulusFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (locatedRealModulus_round_trip x).symm
      (Eq.trans hread (locatedRealModulus_round_trip y)))

private theorem locatedRealModulus_field_faithful :
    ∀ x y : LocatedRealModulusUp, locatedRealModulusFields x = locatedRealModulusFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk located₁ precisionLedger₁ streamWindow₁ readback₁ realSeal₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk located₂ precisionLedger₂ streamWindow₂ readback₂ realSeal₂ transport₂ replay₂
          provenance₂ name₂ =>
          injection hfields with hlocated tail0
          injection tail0 with hprecision tail1
          injection tail1 with hwindow tail2
          injection tail2 with hreadback tail3
          injection tail3 with hseal tail4
          injection tail4 with htransport tail5
          injection tail5 with hreplay tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hname _
          subst hlocated
          subst hprecision
          subst hwindow
          subst hreadback
          subst hseal
          subst htransport
          subst hreplay
          subst hprovenance
          subst hname
          rfl

instance locatedRealModulusBHistCarrier : BHistCarrier LocatedRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := locatedRealModulusToEventFlow
  fromEventFlow := locatedRealModulusFromEventFlow

instance locatedRealModulusChapterTasteGate : ChapterTasteGate LocatedRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) = some x
    exact locatedRealModulus_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (locatedRealModulusToEventFlow_injective heq)

instance locatedRealModulusFieldFaithful : FieldFaithful LocatedRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := locatedRealModulusFields
  field_faithful := locatedRealModulus_field_faithful

instance locatedRealModulusNontrivial : Nontrivial LocatedRealModulusUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LocatedRealModulusUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LocatedRealModulusUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LocatedRealModulusUp :=
  -- BEDC touchpoint anchor: BHist BMark
  locatedRealModulusChapterTasteGate

theorem LocatedRealModulusTasteGate_single_carrier_alignment :
    Nonempty (BEDC.Meta.TasteGate.Nontrivial LocatedRealModulusUp) ∧
      (∀ h : BHist, locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist h) = h) ∧
      (∀ x y : LocatedRealModulusUp, locatedRealModulusFields x = locatedRealModulusFields y →
        x = y) ∧
      (∀ x : LocatedRealModulusUp,
        locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) = some x) ∧
      (∀ x y : LocatedRealModulusUp,
        locatedRealModulusToEventFlow x = locatedRealModulusToEventFlow y → x = y) ∧
      locatedRealModulusEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful ChapterTasteGate
  constructor
  · exact ⟨locatedRealModulusNontrivial⟩
  · constructor
    · intro h
      induction h with
      | Empty => rfl
      | e0 h ih => exact congrArg BHist.e0 ih
      | e1 h ih => exact congrArg BHist.e1 ih
    · constructor
      · intro x y hfields
        cases x with
        | mk located₁ precisionLedger₁ streamWindow₁ readback₁ realSeal₁ transport₁ replay₁
            provenance₁ name₁ =>
            cases y with
            | mk located₂ precisionLedger₂ streamWindow₂ readback₂ realSeal₂ transport₂ replay₂
                provenance₂ name₂ =>
                injection hfields with hlocated tail0
                injection tail0 with hprecision tail1
                injection tail1 with hwindow tail2
                injection tail2 with hreadback tail3
                injection tail3 with hseal tail4
                injection tail4 with htransport tail5
                injection tail5 with hreplay tail6
                injection tail6 with hprovenance tail7
                injection tail7 with hname _
                subst hlocated
                subst hprecision
                subst hwindow
                subst hreadback
                subst hseal
                subst htransport
                subst hreplay
                subst hprovenance
                subst hname
                rfl
      · constructor
        · intro x
          cases x with
          | mk located precisionLedger streamWindow readback realSeal transport replay provenance
              name =>
              change
                some
                    (LocatedRealModulusUp.mk
                      (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist located))
                      (locatedRealModulusDecodeBHist
                        (locatedRealModulusEncodeBHist precisionLedger))
                      (locatedRealModulusDecodeBHist
                        (locatedRealModulusEncodeBHist streamWindow))
                      (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist readback))
                      (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist realSeal))
                      (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist transport))
                      (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist replay))
                      (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist provenance))
                      (locatedRealModulusDecodeBHist (locatedRealModulusEncodeBHist name))) =
                  some
                    (LocatedRealModulusUp.mk located precisionLedger streamWindow readback
                      realSeal transport replay provenance name)
              rw [locatedRealModulus_decode_encode_bhist located]
              rw [locatedRealModulus_decode_encode_bhist precisionLedger]
              rw [locatedRealModulus_decode_encode_bhist streamWindow]
              rw [locatedRealModulus_decode_encode_bhist readback]
              rw [locatedRealModulus_decode_encode_bhist realSeal]
              rw [locatedRealModulus_decode_encode_bhist transport]
              rw [locatedRealModulus_decode_encode_bhist replay]
              rw [locatedRealModulus_decode_encode_bhist provenance]
              rw [locatedRealModulus_decode_encode_bhist name]
        · constructor
          · intro x y heq
            have hread :
                locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) =
                  locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow y) :=
              congrArg locatedRealModulusFromEventFlow heq
            have hx :
                locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow x) =
                  some x := by
              cases x with
              | mk located precisionLedger streamWindow readback realSeal transport replay
                  provenance name =>
                  change
                    some
                        (LocatedRealModulusUp.mk
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist located))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist precisionLedger))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist streamWindow))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist readback))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist realSeal))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist transport))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist replay))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist provenance))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist name))) =
                      some
                        (LocatedRealModulusUp.mk located precisionLedger streamWindow readback
                          realSeal transport replay provenance name)
                  rw [locatedRealModulus_decode_encode_bhist located]
                  rw [locatedRealModulus_decode_encode_bhist precisionLedger]
                  rw [locatedRealModulus_decode_encode_bhist streamWindow]
                  rw [locatedRealModulus_decode_encode_bhist readback]
                  rw [locatedRealModulus_decode_encode_bhist realSeal]
                  rw [locatedRealModulus_decode_encode_bhist transport]
                  rw [locatedRealModulus_decode_encode_bhist replay]
                  rw [locatedRealModulus_decode_encode_bhist provenance]
                  rw [locatedRealModulus_decode_encode_bhist name]
            have hy :
                locatedRealModulusFromEventFlow (locatedRealModulusToEventFlow y) =
                  some y := by
              cases y with
              | mk located precisionLedger streamWindow readback realSeal transport replay
                  provenance name =>
                  change
                    some
                        (LocatedRealModulusUp.mk
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist located))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist precisionLedger))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist streamWindow))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist readback))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist realSeal))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist transport))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist replay))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist provenance))
                          (locatedRealModulusDecodeBHist
                            (locatedRealModulusEncodeBHist name))) =
                      some
                        (LocatedRealModulusUp.mk located precisionLedger streamWindow readback
                          realSeal transport replay provenance name)
                  rw [locatedRealModulus_decode_encode_bhist located]
                  rw [locatedRealModulus_decode_encode_bhist precisionLedger]
                  rw [locatedRealModulus_decode_encode_bhist streamWindow]
                  rw [locatedRealModulus_decode_encode_bhist readback]
                  rw [locatedRealModulus_decode_encode_bhist realSeal]
                  rw [locatedRealModulus_decode_encode_bhist transport]
                  rw [locatedRealModulus_decode_encode_bhist replay]
                  rw [locatedRealModulus_decode_encode_bhist provenance]
                  rw [locatedRealModulus_decode_encode_bhist name]
            exact Option.some.inj (Eq.trans hx.symm (Eq.trans hread hy))
          · rfl

end BEDC.Derived.LocatedRealModulusUp
