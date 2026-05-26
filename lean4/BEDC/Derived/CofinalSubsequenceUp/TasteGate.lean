import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalSubsequenceUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalSubsequenceUp : Type where
  | mk
      (source selector window dyadic regseqHandoff realSeal transport replay provenance
        localNameCert : BHist) :
        CofinalSubsequenceUp
  deriving DecidableEq

def CofinalSubsequenceTasteGate_single_carrier_alignment_tag : RawEvent :=
  -- BEDC touchpoint anchor: BHist BMark
  [BMark.b0, BMark.b1, BMark.b1, BMark.b0]

def CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist h

def CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0
      (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1
      (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
          (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CofinalSubsequenceTasteGate_single_carrier_alignment_fields :
    CofinalSubsequenceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalSubsequenceUp.mk source selector window dyadic regseqHandoff realSeal transport
      replay provenance localNameCert =>
      [source, selector, window, dyadic, regseqHandoff, realSeal, transport, replay,
        provenance, localNameCert]

def CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow :
    CofinalSubsequenceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalSubsequenceUp.mk source selector window dyadic regseqHandoff realSeal transport
      replay provenance localNameCert =>
      [CofinalSubsequenceTasteGate_single_carrier_alignment_tag,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist source,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist selector,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist window,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist dyadic,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist regseqHandoff,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist realSeal,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist transport,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist replay,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist provenance,
        CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist localNameCert]

private def CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt index rest

def CofinalSubsequenceTasteGate_single_carrier_alignment_fromEventFlow :
    EventFlow → Option CofinalSubsequenceUp
  -- BEDC touchpoint anchor: BHist BMark
  | ef =>
      some
        (CofinalSubsequenceUp.mk
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 1 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 2 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 3 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 4 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 5 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 6 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 7 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 8 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 9 ef))
          (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
            (CofinalSubsequenceTasteGate_single_carrier_alignment_eventAt 10 ef)))

private theorem CofinalSubsequenceTasteGate_single_carrier_alignment_round_trip :
    ∀ x : CofinalSubsequenceUp,
      CofinalSubsequenceTasteGate_single_carrier_alignment_fromEventFlow
          (CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk source selector window dyadic regseqHandoff realSeal transport replay provenance
      localNameCert =>
      change
        some
          (CofinalSubsequenceUp.mk
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist source))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist selector))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist window))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist dyadic))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist
                regseqHandoff))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist realSeal))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist transport))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist replay))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist provenance))
            (CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
              (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist
                localNameCert))) =
          some
            (CofinalSubsequenceUp.mk source selector window dyadic regseqHandoff realSeal
              transport replay provenance localNameCert)
      rw [CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode source,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode selector,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode window,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode dyadic,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode regseqHandoff,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode realSeal,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode transport,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode replay,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode provenance,
        CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode localNameCert]

private theorem CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : CofinalSubsequenceUp} :
    CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow x =
        CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CofinalSubsequenceTasteGate_single_carrier_alignment_fromEventFlow
          (CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        CofinalSubsequenceTasteGate_single_carrier_alignment_fromEventFlow
          (CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CofinalSubsequenceTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CofinalSubsequenceTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (CofinalSubsequenceTasteGate_single_carrier_alignment_round_trip y)))

private theorem CofinalSubsequenceTasteGate_single_carrier_alignment_fields_faithful :
    ∀ x y : CofinalSubsequenceUp,
      CofinalSubsequenceTasteGate_single_carrier_alignment_fields x =
          CofinalSubsequenceTasteGate_single_carrier_alignment_fields y →
        x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk source₁ selector₁ window₁ dyadic₁ regseqHandoff₁ realSeal₁ transport₁ replay₁
      provenance₁ localNameCert₁ =>
      cases y with
      | mk source₂ selector₂ window₂ dyadic₂ regseqHandoff₂ realSeal₂ transport₂ replay₂
          provenance₂ localNameCert₂ =>
          cases hfields
          rfl

instance CofinalSubsequenceTasteGate_single_carrier_alignment_BHistCarrier :
    BHistCarrier CofinalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CofinalSubsequenceTasteGate_single_carrier_alignment_fromEventFlow

instance CofinalSubsequenceTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate CofinalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CofinalSubsequenceTasteGate_single_carrier_alignment_fromEventFlow
          (CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow x) =
        some x
    exact CofinalSubsequenceTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CofinalSubsequenceTasteGate_single_carrier_alignment_toEventFlow_injective heq)

instance CofinalSubsequenceTasteGate_single_carrier_alignment_FieldFaithful :
    FieldFaithful CofinalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CofinalSubsequenceTasteGate_single_carrier_alignment_fields
  field_faithful := CofinalSubsequenceTasteGate_single_carrier_alignment_fields_faithful

instance CofinalSubsequenceTasteGate_single_carrier_alignment_Nontrivial :
    Nontrivial CofinalSubsequenceUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CofinalSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CofinalSubsequenceUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def CofinalSubsequenceTasteGate_single_carrier_alignment_taste_gate :
    ChapterTasteGate CofinalSubsequenceUp :=
  -- BEDC touchpoint anchor: BHist BMark
  CofinalSubsequenceTasteGate_single_carrier_alignment_ChapterTasteGate

theorem CofinalSubsequenceTasteGate_single_carrier_alignment :
    (forall h : BHist,
      CofinalSubsequenceTasteGate_single_carrier_alignment_decodeBHist
          (CofinalSubsequenceTasteGate_single_carrier_alignment_encodeBHist h) =
        h) ∧
      CofinalSubsequenceTasteGate_single_carrier_alignment_fields
          (CofinalSubsequenceUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
            BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty) =
        [BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty,
          BHist.Empty, BHist.Empty, BHist.Empty, BHist.Empty] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact CofinalSubsequenceTasteGate_single_carrier_alignment_decode_encode
  · rfl

end BEDC.Derived.CofinalSubsequenceUp
