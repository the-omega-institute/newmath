import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevPoincareFiniteEnergyUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SobolevPoincareFiniteEnergyUp : Type where
  | mk (sobolev poincare domain window energy accounting rational realSeal transport route pkg name :
      BHist) : SobolevPoincareFiniteEnergyUp
  deriving DecidableEq

def sobolevPoincareFiniteEnergyEncodeBHist : BHist -> RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevPoincareFiniteEnergyEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevPoincareFiniteEnergyEncodeBHist h

def sobolevPoincareFiniteEnergyDecodeBHist : RawEvent -> BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevPoincareFiniteEnergyDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevPoincareFiniteEnergyDecodeBHist tail)

private theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode :
    forall h : BHist,
      sobolevPoincareFiniteEnergyDecodeBHist
          (sobolevPoincareFiniteEnergyEncodeBHist h) =
        h := by
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
    SobolevPoincareFiniteEnergyUp -> List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevPoincareFiniteEnergyUp.mk sobolev poincare domain window energy accounting
      rational realSeal transport route pkg name =>
      [sobolev, poincare, domain, window, energy, accounting, rational, realSeal,
        transport, route, pkg, name]

def sobolevPoincareFiniteEnergyToEventFlow :
    SobolevPoincareFiniteEnergyUp -> EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (sobolevPoincareFiniteEnergyFields x).map sobolevPoincareFiniteEnergyEncodeBHist

def sobolevPoincareFiniteEnergyFromEventFlow :
    EventFlow -> Option SobolevPoincareFiniteEnergyUp
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
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            sobolev)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            poincare)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            domain)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            window)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            energy)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            accounting)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            rational)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            realSeal)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            transport)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            route)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            pkg)
                                                          (sobolevPoincareFiniteEnergyDecodeBHist
                                                            name))
                                                  | _ :: _ => none

private theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip :
    forall x : SobolevPoincareFiniteEnergyUp,
      sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk sobolev poincare domain window energy accounting rational realSeal transport route
      pkg name =>
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
          some
            (SobolevPoincareFiniteEnergyUp.mk sobolev poincare domain window energy
              accounting rational realSeal transport route pkg name)
      rw [SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          sobolev,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          poincare,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          domain,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          window,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          energy,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          accounting,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          rational,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          realSeal,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          transport,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          route,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          pkg,
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode
          name]

private theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : SobolevPoincareFiniteEnergyUp} :
    sobolevPoincareFiniteEnergyToEventFlow x =
      sobolevPoincareFiniteEnergyToEventFlow y ->
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow x) =
        sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow y) :=
    congrArg sobolevPoincareFiniteEnergyFromEventFlow heq
  exact Option.some.inj
    (Eq.trans
      (SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip y)))

private theorem SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_fields_faithful :
    forall x y : SobolevPoincareFiniteEnergyUp,
      sobolevPoincareFiniteEnergyFields x =
        sobolevPoincareFiniteEnergyFields y -> x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk sobolev poincare domain window energy accounting rational realSeal transport route
      pkg name =>
      cases y with
      | mk sobolev' poincare' domain' window' energy' accounting' rational' realSeal'
          transport' route' pkg' name' =>
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
          (sobolevPoincareFiniteEnergyToEventFlow x) =
        some x
    exact SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy
      (SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_toEventFlow_injective
        heq)

instance sobolevPoincareFiniteEnergyFieldFaithful :
    FieldFaithful SobolevPoincareFiniteEnergyUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := sobolevPoincareFiniteEnergyFields
  field_faithful :=
    SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_fields_faithful

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
    (forall h : BHist,
        sobolevPoincareFiniteEnergyDecodeBHist
          (sobolevPoincareFiniteEnergyEncodeBHist h) = h) ∧
      (forall x : SobolevPoincareFiniteEnergyUp,
        sobolevPoincareFiniteEnergyFromEventFlow
          (sobolevPoincareFiniteEnergyToEventFlow x) = some x) ∧
        (forall {x y : SobolevPoincareFiniteEnergyUp},
          sobolevPoincareFiniteEnergyToEventFlow x =
            sobolevPoincareFiniteEnergyToEventFlow y -> x = y) ∧
          Nonempty (BHistCarrier SobolevPoincareFiniteEnergyUp) ∧
            Nonempty (ChapterTasteGate SobolevPoincareFiniteEnergyUp) ∧
              Nonempty (FieldFaithful SobolevPoincareFiniteEnergyUp) ∧
                Nonempty (Nontrivial SobolevPoincareFiniteEnergyUp) ∧
                  sobolevPoincareFiniteEnergyEncodeBHist BHist.Empty =
                    ([] : List BMark) ∧
                    sobolevPoincareFiniteEnergyDecodeBHist [BMark.b1] =
                      BHist.e1 BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  exact
    ⟨SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_decode_encode,
      SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_round_trip,
      fun {x} {y} heq =>
        SobolevPoincareFiniteEnergyTasteGate_single_carrier_alignment_toEventFlow_injective
          heq,
      ⟨sobolevPoincareFiniteEnergyBHistCarrier⟩,
      ⟨sobolevPoincareFiniteEnergyChapterTasteGate⟩,
      ⟨sobolevPoincareFiniteEnergyFieldFaithful⟩,
      ⟨sobolevPoincareFiniteEnergyNontrivial⟩,
      rfl,
      rfl⟩

end BEDC.Derived.SobolevPoincareFiniteEnergyUp.TasteGate
