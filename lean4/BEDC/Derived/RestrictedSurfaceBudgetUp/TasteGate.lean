import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RestrictedSurfaceBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RestrictedSurfaceBudgetUp : Type where
  | mk
      (claim restrictedSurface witness supply nonExport transport replay provenance name :
        BHist) :
      RestrictedSurfaceBudgetUp
  deriving DecidableEq

def restrictedSurfaceBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: restrictedSurfaceBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: restrictedSurfaceBudgetEncodeBHist h

def restrictedSurfaceBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (restrictedSurfaceBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (restrictedSurfaceBudgetDecodeBHist tail)

private theorem restrictedSurfaceBudget_decode_encode_bhist :
    ∀ h : BHist,
      restrictedSurfaceBudgetDecodeBHist (restrictedSurfaceBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem restrictedSurfaceBudget_mk_congr
    {claim claim' restrictedSurface restrictedSurface' witness witness' supply supply'
      nonExport nonExport' transport transport' replay replay' provenance provenance'
      name name' : BHist}
    (hClaim : claim' = claim)
    (hRestrictedSurface : restrictedSurface' = restrictedSurface)
    (hWitness : witness' = witness)
    (hSupply : supply' = supply)
    (hNonExport : nonExport' = nonExport)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    RestrictedSurfaceBudgetUp.mk claim' restrictedSurface' witness' supply' nonExport'
        transport' replay' provenance' name' =
      RestrictedSurfaceBudgetUp.mk claim restrictedSurface witness supply nonExport transport
        replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hClaim
  cases hRestrictedSurface
  cases hWitness
  cases hSupply
  cases hNonExport
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def restrictedSurfaceBudgetFields : RestrictedSurfaceBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RestrictedSurfaceBudgetUp.mk claim restrictedSurface witness supply nonExport transport
      replay provenance name =>
      [claim, restrictedSurface, witness, supply, nonExport, transport, replay,
        provenance, name]

def restrictedSurfaceBudgetToEventFlow : RestrictedSurfaceBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (restrictedSurfaceBudgetFields x).map restrictedSurfaceBudgetEncodeBHist

def restrictedSurfaceBudgetFromEventFlow :
    EventFlow → Option RestrictedSurfaceBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | claim :: rest0 =>
      match rest0 with
      | [] => none
      | restrictedSurface :: rest1 =>
          match rest1 with
          | [] => none
          | witness :: rest2 =>
              match rest2 with
              | [] => none
              | supply :: rest3 =>
                  match rest3 with
                  | [] => none
                  | nonExport :: rest4 =>
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
                                            (RestrictedSurfaceBudgetUp.mk
                                              (restrictedSurfaceBudgetDecodeBHist claim)
                                              (restrictedSurfaceBudgetDecodeBHist
                                                restrictedSurface)
                                              (restrictedSurfaceBudgetDecodeBHist witness)
                                              (restrictedSurfaceBudgetDecodeBHist supply)
                                              (restrictedSurfaceBudgetDecodeBHist nonExport)
                                              (restrictedSurfaceBudgetDecodeBHist transport)
                                              (restrictedSurfaceBudgetDecodeBHist replay)
                                              (restrictedSurfaceBudgetDecodeBHist provenance)
                                              (restrictedSurfaceBudgetDecodeBHist name))
                                      | _ :: _ => none

private theorem restrictedSurfaceBudget_round_trip :
    ∀ x : RestrictedSurfaceBudgetUp,
      restrictedSurfaceBudgetFromEventFlow
        (restrictedSurfaceBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk claim restrictedSurface witness supply nonExport transport replay provenance name =>
      change
        some
          (RestrictedSurfaceBudgetUp.mk
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist claim))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist restrictedSurface))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist witness))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist supply))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist nonExport))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist transport))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist replay))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist provenance))
            (restrictedSurfaceBudgetDecodeBHist
              (restrictedSurfaceBudgetEncodeBHist name))) =
          some
            (RestrictedSurfaceBudgetUp.mk claim restrictedSurface witness supply nonExport
              transport replay provenance name)
      exact
        congrArg some
          (restrictedSurfaceBudget_mk_congr
            (restrictedSurfaceBudget_decode_encode_bhist claim)
            (restrictedSurfaceBudget_decode_encode_bhist restrictedSurface)
            (restrictedSurfaceBudget_decode_encode_bhist witness)
            (restrictedSurfaceBudget_decode_encode_bhist supply)
            (restrictedSurfaceBudget_decode_encode_bhist nonExport)
            (restrictedSurfaceBudget_decode_encode_bhist transport)
            (restrictedSurfaceBudget_decode_encode_bhist replay)
            (restrictedSurfaceBudget_decode_encode_bhist provenance)
            (restrictedSurfaceBudget_decode_encode_bhist name))

private theorem restrictedSurfaceBudgetToEventFlow_injective
    {x y : RestrictedSurfaceBudgetUp} :
    restrictedSurfaceBudgetToEventFlow x =
      restrictedSurfaceBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      restrictedSurfaceBudgetFromEventFlow
          (restrictedSurfaceBudgetToEventFlow x) =
        restrictedSurfaceBudgetFromEventFlow
          (restrictedSurfaceBudgetToEventFlow y) :=
    congrArg restrictedSurfaceBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (restrictedSurfaceBudget_round_trip x).symm
      (Eq.trans hread (restrictedSurfaceBudget_round_trip y)))

private theorem restrictedSurfaceBudget_fields_faithful :
    ∀ x y : RestrictedSurfaceBudgetUp,
      restrictedSurfaceBudgetFields x = restrictedSurfaceBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y h
  cases x with
  | mk claim₁ restrictedSurface₁ witness₁ supply₁ nonExport₁ transport₁ replay₁
      provenance₁ name₁ =>
      cases y with
      | mk claim₂ restrictedSurface₂ witness₂ supply₂ nonExport₂ transport₂ replay₂
          provenance₂ name₂ =>
          simp only [restrictedSurfaceBudgetFields] at h
          cases h
          rfl

instance restrictedSurfaceBudgetBHistCarrier :
    BHistCarrier RestrictedSurfaceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := restrictedSurfaceBudgetToEventFlow
  fromEventFlow := restrictedSurfaceBudgetFromEventFlow

instance restrictedSurfaceBudgetChapterTasteGate :
    ChapterTasteGate RestrictedSurfaceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      restrictedSurfaceBudgetFromEventFlow
        (restrictedSurfaceBudgetToEventFlow x) = some x
    exact restrictedSurfaceBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (restrictedSurfaceBudgetToEventFlow_injective heq)

instance restrictedSurfaceBudgetFieldFaithful :
    FieldFaithful RestrictedSurfaceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := restrictedSurfaceBudgetFields
  field_faithful := restrictedSurfaceBudget_fields_faithful

instance restrictedSurfaceBudgetNontrivial :
    Nontrivial RestrictedSurfaceBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RestrictedSurfaceBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RestrictedSurfaceBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate RestrictedSurfaceBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  restrictedSurfaceBudgetChapterTasteGate

theorem RestrictedSurfaceBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist,
      restrictedSurfaceBudgetDecodeBHist (restrictedSurfaceBudgetEncodeBHist h) = h) ∧
      (∀ x : RestrictedSurfaceBudgetUp,
        restrictedSurfaceBudgetFromEventFlow
          (restrictedSurfaceBudgetToEventFlow x) = some x) ∧
        (∀ x y : RestrictedSurfaceBudgetUp,
          restrictedSurfaceBudgetToEventFlow x =
            restrictedSurfaceBudgetToEventFlow y → x = y) ∧
          restrictedSurfaceBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact restrictedSurfaceBudget_decode_encode_bhist
  · constructor
    · exact restrictedSurfaceBudget_round_trip
    · constructor
      · intro x y heq
        exact restrictedSurfaceBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.RestrictedSurfaceBudgetUp
