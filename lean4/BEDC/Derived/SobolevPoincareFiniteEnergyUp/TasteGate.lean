import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevPoincareFiniteEnergyUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevPoincareFiniteEnergyUp : Type where
  | mk (sobolev poincare domain window energy accounting rational realSeal transport route pkg name : BHist) : SobolevPoincareFiniteEnergyUp
  deriving DecidableEq

def sobolevPoincareFiniteEnergyEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevPoincareFiniteEnergyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevPoincareFiniteEnergyEncodeBHist h

def sobolevPoincareFiniteEnergyDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevPoincareFiniteEnergyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevPoincareFiniteEnergyDecodeBHist tail)

private theorem sobolevPoincareFiniteEnergy_decode_encode_bhist :
    ∀ h : BHist,
      sobolevPoincareFiniteEnergyDecodeBHist
        (sobolevPoincareFiniteEnergyEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def sobolevPoincareFiniteEnergyFields :
    SobolevPoincareFiniteEnergyUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevPoincareFiniteEnergyUp.mk sobolev poincare domain window energy accounting rational realSeal transport route pkg name =>
      [sobolev, poincare, domain, window, energy, accounting, rational, realSeal, transport, route, pkg, name]

def sobolevPoincareFiniteEnergyToEventFlow :
    SobolevPoincareFiniteEnergyUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sobolevPoincareFiniteEnergyFields x).map
      sobolevPoincareFiniteEnergyEncodeBHist

def sobolevPoincareFiniteEnergyFromEventFlow :
    EventFlow → Option SobolevPoincareFiniteEnergyUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | sobolev :: rest =>
      match rest with
      | [] => none
      | poincare :: rest =>
          match rest with
          | [] => none
          | domain :: rest =>
              match rest with
              | [] => none
              | window :: rest =>
                  match rest with
                  | [] => none
                  | energy :: rest =>
                      match rest with
                      | [] => none
                      | accounting :: rest =>
                          match rest with
                          | [] => none
                          | rational :: rest =>
                              match rest with
                              | [] => none
                              | realSeal :: rest =>
                                  match rest with
                                  | [] => none
                                  | transport :: rest =>
                                      match rest with
                                      | [] => none
                                      | route :: rest =>
                                          match rest with
                                          | [] => none
                                          | pkg :: rest =>
                                              match rest with
                                              | [] => none
                                              | name :: rest =>
                                                  match rest with
                                                  | [] =>
                                                      some
                                                        (SobolevPoincareFiniteEnergyUp.mk
                                                          (sobolevPoincareFiniteEnergyDecodeBHist sobolev)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist poincare)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist domain)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist window)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist energy)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist accounting)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist rational)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist realSeal)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist transport)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist route)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist pkg)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist name))
                                                  | _ :: _ => none

private theorem sobolevPoincareFiniteEnergy_round_trip :
    ∀ x : SobolevPoincareFiniteEnergyUp,
      sobolevPoincareFiniteEnergyFromEventFlow
        (sobolevPoincareFiniteEnergyToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sobolev poincare domain window energy accounting rational realSeal transport route pkg name =>
      change
        some
          (SobolevPoincareFiniteEnergyUp.mk
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist sobolev))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist poincare))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist domain))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist window))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist energy))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist accounting))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist rational))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist realSeal))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist transport))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist route))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist pkg))
            (sobolevPoincareFiniteEnergyDecodeBHist
              (sobolevPoincareFiniteEnergyEncodeBHist name))) =
          some (SobolevPoincareFiniteEnergyUp.mk sobolev poincare domain window energy accounting rational realSeal transport route pkg name)
      rw [sobolevPoincareFiniteEnergy_decode_encode_bhist sobolev,
        sobolevPoincareFiniteEnergy_decode_encode_bhist poincare,
        sobolevPoincareFiniteEnergy_decode_encode_bhist domain,
        sobolevPoincareFiniteEnergy_decode_encode_bhist window,
        sobolevPoincareFiniteEnergy_decode_encode_bhist energy,
        sobolevPoincareFiniteEnergy_decode_encode_bhist accounting,
        sobolevPoincareFiniteEnergy_decode_encode_bhist rational,
        sobolevPoincareFiniteEnergy_decode_encode_bhist realSeal,
        sobolevPoincareFiniteEnergy_decode_encode_bhist transport,
        sobolevPoincareFiniteEnergy_decode_encode_bhist route,
        sobolevPoincareFiniteEnergy_decode_encode_bhist pkg,
        sobolevPoincareFiniteEnergy_decode_encode_bhist name]

private theorem sobolevPoincareFiniteEnergyToEventFlow_injective
    {x y : SobolevPoincareFiniteEnergyUp} :
    sobolevPoincareFiniteEnergyToEventFlow x =
      sobolevPoincareFiniteEnergyToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow x) =
        sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow y) :=
    congrArg sobolevPoincareFiniteEnergyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sobolevPoincareFiniteEnergy_round_trip x).symm
      (Eq.trans hread (sobolevPoincareFiniteEnergy_round_trip y)))

private theorem sobolevPoincareFiniteEnergy_fields_faithful :
    ∀ x y : SobolevPoincareFiniteEnergyUp,
      sobolevPoincareFiniteEnergyFields x =
        sobolevPoincareFiniteEnergyFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sobolev poincare domain window energy accounting rational realSeal transport route pkg name =>
      cases y with
      | mk sobolev' poincare' domain' window' energy' accounting' rational' realSeal' transport' route' pkg' name' =>
          cases hfields
          rfl

instance sobolevPoincareFiniteEnergyBHistCarrier :
    BHistCarrier SobolevPoincareFiniteEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevPoincareFiniteEnergyToEventFlow
  fromEventFlow := sobolevPoincareFiniteEnergyFromEventFlow

instance sobolevPoincareFiniteEnergyChapterTasteGate :
    ChapterTasteGate SobolevPoincareFiniteEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      sobolevPoincareFiniteEnergyFromEventFlow
        (sobolevPoincareFiniteEnergyToEventFlow x) = some x
    exact sobolevPoincareFiniteEnergy_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sobolevPoincareFiniteEnergyToEventFlow_injective heq)

instance sobolevPoincareFiniteEnergyFieldFaithful :
    FieldFaithful SobolevPoincareFiniteEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sobolevPoincareFiniteEnergyFields
  field_faithful := sobolevPoincareFiniteEnergy_fields_faithful

instance sobolevPoincareFiniteEnergyNontrivial :
    Nontrivial SobolevPoincareFiniteEnergyUp where
  witness_pair :=
    ⟨SobolevPoincareFiniteEnergyUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      SobolevPoincareFiniteEnergyUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty,
      by
        -- BEDC touchpoint anchor: BHist BMark
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate SobolevPoincareFiniteEnergyUp :=
  -- BEDC touchpoint anchor: BHist BMark
  sobolevPoincareFiniteEnergyChapterTasteGate

theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment :
    (∀ h : BHist,
        sobolevPoincareFiniteEnergyDecodeBHist
          (sobolevPoincareFiniteEnergyEncodeBHist h) = h) ∧
      Nonempty (BHistCarrier SobolevPoincareFiniteEnergyUp) ∧
        Nonempty (ChapterTasteGate SobolevPoincareFiniteEnergyUp) ∧
          sobolevPoincareFiniteEnergyEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  exact
    ⟨sobolevPoincareFiniteEnergy_decode_encode_bhist,
      ⟨sobolevPoincareFiniteEnergyBHistCarrier⟩,
      ⟨sobolevPoincareFiniteEnergyChapterTasteGate⟩,
      rfl⟩

end BEDC.Derived.SobolevPoincareFiniteEnergyUp
