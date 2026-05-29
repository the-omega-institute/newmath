import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.RealApartnessSignUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive RealApartnessSignUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (inspected apartness window readback dyadic realSeal located transport replay provenance
      name : BHist) : RealApartnessSignUp
  deriving DecidableEq

def realApartnessSignEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: realApartnessSignEncodeBHist h
  | BHist.e1 h => BMark.b1 :: realApartnessSignEncodeBHist h

def realApartnessSignDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (realApartnessSignDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (realApartnessSignDecodeBHist tail)

private theorem RealApartnessSignTasteGate_single_carrier_alignment_decode :
    ∀ h : BHist, realApartnessSignDecodeBHist (realApartnessSignEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def realApartnessSignToEventFlow : RealApartnessSignUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | RealApartnessSignUp.mk inspected apartness window readback dyadic realSeal located transport replay
      provenance name =>
      [[BMark.b0],
        realApartnessSignEncodeBHist inspected,
        [BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist apartness,
        [BMark.b1, BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist dyadic,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist located,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        realApartnessSignEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        realApartnessSignEncodeBHist name]

private def realApartnessSignDecodePacket
    (inspected apartness window readback dyadic realSeal located transport replay provenance
      name : RawEvent) : RealApartnessSignUp :=
  -- BEDC touchpoint anchor: BHist BMark
  RealApartnessSignUp.mk
    (realApartnessSignDecodeBHist inspected)
    (realApartnessSignDecodeBHist apartness)
    (realApartnessSignDecodeBHist window)
    (realApartnessSignDecodeBHist readback)
    (realApartnessSignDecodeBHist dyadic)
    (realApartnessSignDecodeBHist realSeal)
    (realApartnessSignDecodeBHist located)
    (realApartnessSignDecodeBHist transport)
    (realApartnessSignDecodeBHist replay)
    (realApartnessSignDecodeBHist provenance)
    (realApartnessSignDecodeBHist name)

private def RealApartnessSignTasteGate_single_carrier_alignment_readPair
    (ef : EventFlow) : Option (RawEvent × EventFlow) :=
  -- BEDC touchpoint anchor: BHist BMark
  match ef with
  | [] => none
  | _tag :: rest0 =>
      match rest0 with
      | [] => none
      | value :: rest => some (value, rest)

def realApartnessSignFromEventFlow : EventFlow → Option RealApartnessSignUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      match RealApartnessSignTasteGate_single_carrier_alignment_readPair ef with
      | none => none
      | some (inspected, rest0) =>
          match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest0 with
          | none => none
          | some (apartness, rest1) =>
              match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest1 with
              | none => none
              | some (window, rest2) =>
                  match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest2 with
                  | none => none
                  | some (readback, rest3) =>
                      match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest3 with
                      | none => none
                      | some (dyadic, rest4) =>
                          match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest4 with
                          | none => none
                          | some (realSeal, rest5) =>
                              match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest5 with
                              | none => none
                              | some (located, rest6) =>
                                  match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest6 with
                                  | none => none
                                  | some (transport, rest7) =>
                                      match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest7 with
                                      | none => none
                                      | some (replay, rest8) =>
                                          match RealApartnessSignTasteGate_single_carrier_alignment_readPair rest8 with
                                          | none => none
                                          | some (provenance, rest9) =>
                                              match
                                                RealApartnessSignTasteGate_single_carrier_alignment_readPair
                                                  rest9
                                              with
                                              | none => none
                                              | some (name, rest10) =>
                                                  match rest10 with
                                                  | [] =>
                                                      some
                                                        (realApartnessSignDecodePacket inspected
                                                          apartness window readback dyadic
                                                          realSeal located transport replay
                                                          provenance name)
                                                  | _ :: _ => none

private theorem RealApartnessSignTasteGate_single_carrier_alignment_round_trip :
    ∀ x : RealApartnessSignUp,
      realApartnessSignFromEventFlow (realApartnessSignToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk inspected apartness window readback dyadic realSeal located transport replay provenance name =>
      change
        some
          (realApartnessSignDecodePacket
            (realApartnessSignEncodeBHist inspected)
            (realApartnessSignEncodeBHist apartness)
            (realApartnessSignEncodeBHist window)
            (realApartnessSignEncodeBHist readback)
            (realApartnessSignEncodeBHist dyadic)
            (realApartnessSignEncodeBHist realSeal)
            (realApartnessSignEncodeBHist located)
            (realApartnessSignEncodeBHist transport)
            (realApartnessSignEncodeBHist replay)
            (realApartnessSignEncodeBHist provenance)
            (realApartnessSignEncodeBHist name)) =
          some
            (RealApartnessSignUp.mk inspected apartness window readback dyadic realSeal located
              transport replay provenance name)
      unfold realApartnessSignDecodePacket
      rw [RealApartnessSignTasteGate_single_carrier_alignment_decode inspected,
        RealApartnessSignTasteGate_single_carrier_alignment_decode apartness,
        RealApartnessSignTasteGate_single_carrier_alignment_decode window,
        RealApartnessSignTasteGate_single_carrier_alignment_decode readback,
        RealApartnessSignTasteGate_single_carrier_alignment_decode dyadic,
        RealApartnessSignTasteGate_single_carrier_alignment_decode realSeal,
        RealApartnessSignTasteGate_single_carrier_alignment_decode located,
        RealApartnessSignTasteGate_single_carrier_alignment_decode transport,
        RealApartnessSignTasteGate_single_carrier_alignment_decode replay,
        RealApartnessSignTasteGate_single_carrier_alignment_decode provenance,
        RealApartnessSignTasteGate_single_carrier_alignment_decode name]

private theorem RealApartnessSignTasteGate_single_carrier_alignment_injective
    {x y : RealApartnessSignUp} :
    realApartnessSignToEventFlow x = realApartnessSignToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      realApartnessSignFromEventFlow (realApartnessSignToEventFlow x) =
        realApartnessSignFromEventFlow (realApartnessSignToEventFlow y) :=
    congrArg realApartnessSignFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (RealApartnessSignTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (RealApartnessSignTasteGate_single_carrier_alignment_round_trip y)))

instance realApartnessSignBHistCarrier : BHistCarrier RealApartnessSignUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := realApartnessSignToEventFlow
  fromEventFlow := realApartnessSignFromEventFlow

instance realApartnessSignChapterTasteGate : ChapterTasteGate RealApartnessSignUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change realApartnessSignFromEventFlow (realApartnessSignToEventFlow x) = some x
    exact RealApartnessSignTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (RealApartnessSignTasteGate_single_carrier_alignment_injective heq)

instance realApartnessSignFieldFaithful : FieldFaithful RealApartnessSignUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | RealApartnessSignUp.mk inspected apartness window readback dyadic realSeal located transport
        replay provenance name =>
        [inspected, apartness, window, readback, dyadic, realSeal, located, transport, replay,
          provenance, name]
  field_faithful := by
    intro x y hfields
    cases x with
    | mk inspected1 apartness1 window1 readback1 dyadic1 seal1 located1 transport1 replay1
        provenance1 name1 =>
        cases y with
        | mk inspected2 apartness2 window2 readback2 dyadic2 seal2 located2 transport2 replay2
            provenance2 name2 =>
            cases hfields
            rfl

instance realApartnessSignNontrivial : Nontrivial RealApartnessSignUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨RealApartnessSignUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      RealApartnessSignUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem RealApartnessSignTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate RealApartnessSignUp) ∧
      Nonempty (FieldFaithful RealApartnessSignUp) ∧
        Nonempty (Nontrivial RealApartnessSignUp) ∧
          (∀ h : BHist, realApartnessSignDecodeBHist (realApartnessSignEncodeBHist h) = h) ∧
            (∀ x : RealApartnessSignUp,
              realApartnessSignFromEventFlow (realApartnessSignToEventFlow x) = some x) ∧
              (∀ x y : RealApartnessSignUp,
                realApartnessSignToEventFlow x = realApartnessSignToEventFlow y → x = y) ∧
                realApartnessSignEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨realApartnessSignChapterTasteGate⟩
  · constructor
    · exact ⟨realApartnessSignFieldFaithful⟩
    · constructor
      · exact ⟨realApartnessSignNontrivial⟩
      · constructor
        · exact RealApartnessSignTasteGate_single_carrier_alignment_decode
        · constructor
          · exact RealApartnessSignTasteGate_single_carrier_alignment_round_trip
          · constructor
            · intro x y heq
              exact RealApartnessSignTasteGate_single_carrier_alignment_injective heq
            · rfl

end BEDC.Derived.RealApartnessSignUp.TasteGate
