import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.PoissonKernelUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive PoissonKernelUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (radius angle denominator numerator value fejer dirichlet transport replay provenance
      name : BHist) : PoissonKernelUp
  deriving DecidableEq

def poissonKernelEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: poissonKernelEncodeBHist h
  | BHist.e1 h => BMark.b1 :: poissonKernelEncodeBHist h

def poissonKernelDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (poissonKernelDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (poissonKernelDecodeBHist tail)

private theorem PoissonKernelTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, poissonKernelDecodeBHist (poissonKernelEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def poissonKernelToEventFlow : PoissonKernelUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | PoissonKernelUp.mk radius angle denominator numerator value fejer dirichlet transport replay
      provenance name =>
      [[BMark.b0],
        poissonKernelEncodeBHist radius,
        [BMark.b1, BMark.b0],
        poissonKernelEncodeBHist angle,
        [BMark.b1, BMark.b1, BMark.b0],
        poissonKernelEncodeBHist denominator,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        poissonKernelEncodeBHist numerator,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        poissonKernelEncodeBHist value,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        poissonKernelEncodeBHist fejer,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        poissonKernelEncodeBHist dirichlet,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        poissonKernelEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        poissonKernelEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        poissonKernelEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        poissonKernelEncodeBHist name]

private def poissonKernelDecodePacket
    (radius angle denominator numerator value fejer dirichlet transport replay provenance
      name : RawEvent) : PoissonKernelUp :=
  -- BEDC touchpoint anchor: BHist BMark
  PoissonKernelUp.mk
    (poissonKernelDecodeBHist radius)
    (poissonKernelDecodeBHist angle)
    (poissonKernelDecodeBHist denominator)
    (poissonKernelDecodeBHist numerator)
    (poissonKernelDecodeBHist value)
    (poissonKernelDecodeBHist fejer)
    (poissonKernelDecodeBHist dirichlet)
    (poissonKernelDecodeBHist transport)
    (poissonKernelDecodeBHist replay)
    (poissonKernelDecodeBHist provenance)
    (poissonKernelDecodeBHist name)

private def PoissonKernelTasteGate_single_carrier_alignment_readPair
    (ef : EventFlow) : Option (RawEvent × EventFlow) :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | value :: rest => some (value, rest)

def poissonKernelFromEventFlow : EventFlow → Option PoissonKernelUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      match PoissonKernelTasteGate_single_carrier_alignment_readPair ef with
      | none => none
      | some (radius, rest0) =>
          match PoissonKernelTasteGate_single_carrier_alignment_readPair rest0 with
          | none => none
          | some (angle, rest1) =>
              match PoissonKernelTasteGate_single_carrier_alignment_readPair rest1 with
              | none => none
              | some (denominator, rest2) =>
                  match PoissonKernelTasteGate_single_carrier_alignment_readPair rest2 with
                  | none => none
                  | some (numerator, rest3) =>
                      match PoissonKernelTasteGate_single_carrier_alignment_readPair rest3 with
                      | none => none
                      | some (value, rest4) =>
                          match PoissonKernelTasteGate_single_carrier_alignment_readPair rest4 with
                          | none => none
                          | some (fejer, rest5) =>
                              match PoissonKernelTasteGate_single_carrier_alignment_readPair rest5 with
                              | none => none
                              | some (dirichlet, rest6) =>
                                  match PoissonKernelTasteGate_single_carrier_alignment_readPair rest6 with
                                  | none => none
                                  | some (transport, rest7) =>
                                      match PoissonKernelTasteGate_single_carrier_alignment_readPair rest7 with
                                      | none => none
                                      | some (replay, rest8) =>
                                          match PoissonKernelTasteGate_single_carrier_alignment_readPair rest8 with
                                          | none => none
                                          | some (provenance, rest9) =>
                                              match
                                                PoissonKernelTasteGate_single_carrier_alignment_readPair
                                                  rest9
                                              with
                                              | none => none
                                              | some (name, rest10) =>
                                                  match rest10 with
                                                  | [] =>
                                                      some
                                                        (poissonKernelDecodePacket radius angle
                                                          denominator numerator value fejer
                                                          dirichlet transport replay provenance
                                                          name)
                                                  | _ :: _ => none

private theorem PoissonKernelTasteGate_single_carrier_alignment_round_trip :
    ∀ x : PoissonKernelUp,
      poissonKernelFromEventFlow (poissonKernelToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk radius angle denominator numerator value fejer dirichlet transport replay provenance name =>
      change
        some
          (poissonKernelDecodePacket
            (poissonKernelEncodeBHist radius)
            (poissonKernelEncodeBHist angle)
            (poissonKernelEncodeBHist denominator)
            (poissonKernelEncodeBHist numerator)
            (poissonKernelEncodeBHist value)
            (poissonKernelEncodeBHist fejer)
            (poissonKernelEncodeBHist dirichlet)
            (poissonKernelEncodeBHist transport)
            (poissonKernelEncodeBHist replay)
            (poissonKernelEncodeBHist provenance)
            (poissonKernelEncodeBHist name)) =
          some
            (PoissonKernelUp.mk radius angle denominator numerator value fejer dirichlet
              transport replay provenance name)
      unfold poissonKernelDecodePacket
      rw [PoissonKernelTasteGate_single_carrier_alignment_decode radius,
        PoissonKernelTasteGate_single_carrier_alignment_decode angle,
        PoissonKernelTasteGate_single_carrier_alignment_decode denominator,
        PoissonKernelTasteGate_single_carrier_alignment_decode numerator,
        PoissonKernelTasteGate_single_carrier_alignment_decode value,
        PoissonKernelTasteGate_single_carrier_alignment_decode fejer,
        PoissonKernelTasteGate_single_carrier_alignment_decode dirichlet,
        PoissonKernelTasteGate_single_carrier_alignment_decode transport,
        PoissonKernelTasteGate_single_carrier_alignment_decode replay,
        PoissonKernelTasteGate_single_carrier_alignment_decode provenance,
        PoissonKernelTasteGate_single_carrier_alignment_decode name]

private theorem PoissonKernelTasteGate_single_carrier_alignment_injective
    {x y : PoissonKernelUp} :
    poissonKernelToEventFlow x = poissonKernelToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      poissonKernelFromEventFlow (poissonKernelToEventFlow x) =
        poissonKernelFromEventFlow (poissonKernelToEventFlow y) :=
    congrArg poissonKernelFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (PoissonKernelTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (PoissonKernelTasteGate_single_carrier_alignment_round_trip y)))

instance poissonKernelBHistCarrier : BHistCarrier PoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := poissonKernelToEventFlow
  fromEventFlow := poissonKernelFromEventFlow

instance poissonKernelChapterTasteGate : ChapterTasteGate PoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change poissonKernelFromEventFlow (poissonKernelToEventFlow x) = some x
    exact PoissonKernelTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (PoissonKernelTasteGate_single_carrier_alignment_injective heq)

instance poissonKernelFieldFaithful : FieldFaithful PoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | PoissonKernelUp.mk radius angle denominator numerator value fejer dirichlet transport
        replay provenance name =>
        [radius, angle, denominator, numerator, value, fejer, dirichlet, transport, replay,
          provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk radius1 angle1 denominator1 numerator1 value1 fejer1 dirichlet1 transport1 replay1
        provenance1 name1 =>
        cases y with
        | mk radius2 angle2 denominator2 numerator2 value2 fejer2 dirichlet2 transport2 replay2
            provenance2 name2 =>
            cases hfields
            rfl

instance poissonKernelNontrivial : Nontrivial PoissonKernelUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨PoissonKernelUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      PoissonKernelUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem PoissonKernelTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate PoissonKernelUp) ∧
      Nonempty (FieldFaithful PoissonKernelUp) ∧
        Nonempty (Nontrivial PoissonKernelUp) ∧
          (∀ h : BHist, poissonKernelDecodeBHist (poissonKernelEncodeBHist h) = h) ∧
            (∀ x : PoissonKernelUp,
              poissonKernelFromEventFlow (poissonKernelToEventFlow x) = some x) ∧
              (∀ x y : PoissonKernelUp,
                poissonKernelToEventFlow x = poissonKernelToEventFlow y → x = y) ∧
                poissonKernelEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨poissonKernelChapterTasteGate⟩
  · constructor
    · exact ⟨poissonKernelFieldFaithful⟩
    · constructor
      · exact ⟨poissonKernelNontrivial⟩
      · constructor
        · exact PoissonKernelTasteGate_single_carrier_alignment_decode
        · constructor
          · exact PoissonKernelTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact PoissonKernelTasteGate_single_carrier_alignment_injective heq
            · rfl

end BEDC.Derived.PoissonKernelUp.TasteGate
