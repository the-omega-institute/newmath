import BEDC.Derived.KKTUp
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.Meta.TasteGate

namespace BEDC.Derived.KKTUp

open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive KKTUp : Type where
  | mk (row route : BHist) : KKTUp
  deriving DecidableEq

def KKTTasteGate_single_carrier_alignment_encodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: KKTTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 :: KKTTasteGate_single_carrier_alignment_encodeBHist h

def KKTTasteGate_single_carrier_alignment_decodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (KKTTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (KKTTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem KKTTasteGate_single_carrier_alignment_decode_encode
    (h : BHist) :
    KKTTasteGate_single_carrier_alignment_decodeBHist
      (KKTTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def KKTTasteGate_single_carrier_alignment_fields : KKTUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | KKTUp.mk row route => [row, route]

def KKTTasteGate_single_carrier_alignment_toEventFlow : KKTUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | packet =>
      List.map KKTTasteGate_single_carrier_alignment_encodeBHist
        (KKTTasteGate_single_carrier_alignment_fields packet)

private def KKTTasteGate_single_carrier_alignment_eventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      KKTTasteGate_single_carrier_alignment_eventAt index rest

def KKTTasteGate_single_carrier_alignment_fromEventFlow : EventFlow → Option KKTUp :=
  -- BEDC touchpoint anchor: BHist BMark
  fun flow =>
    some
      (KKTUp.mk
        (KKTTasteGate_single_carrier_alignment_decodeBHist
          (KKTTasteGate_single_carrier_alignment_eventAt 0 flow))
        (KKTTasteGate_single_carrier_alignment_decodeBHist
          (KKTTasteGate_single_carrier_alignment_eventAt 1 flow)))

private theorem KKTTasteGate_single_carrier_alignment_round_trip
    (packet : KKTUp) :
    KKTTasteGate_single_carrier_alignment_fromEventFlow
      (KKTTasteGate_single_carrier_alignment_toEventFlow packet) = some packet := by
  -- BEDC touchpoint anchor: BHist BMark
  cases packet with
  | mk row route =>
      change
        some
          (KKTUp.mk
            (KKTTasteGate_single_carrier_alignment_decodeBHist
              (KKTTasteGate_single_carrier_alignment_encodeBHist row))
            (KKTTasteGate_single_carrier_alignment_decodeBHist
              (KKTTasteGate_single_carrier_alignment_encodeBHist route))) =
          some (KKTUp.mk row route)
      rw [KKTTasteGate_single_carrier_alignment_decode_encode row,
        KKTTasteGate_single_carrier_alignment_decode_encode route]

private theorem KKTTasteGate_single_carrier_alignment_toEventFlow_injective
    {x y : KKTUp} :
    KKTTasteGate_single_carrier_alignment_toEventFlow x =
      KKTTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      KKTTasteGate_single_carrier_alignment_fromEventFlow
          (KKTTasteGate_single_carrier_alignment_toEventFlow x) =
        KKTTasteGate_single_carrier_alignment_fromEventFlow
          (KKTTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg KKTTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (KKTTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread (KKTTasteGate_single_carrier_alignment_round_trip y)))

instance KKTTasteGate_single_carrier_alignment_BHistCarrier : BHistCarrier KKTUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := KKTTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := KKTTasteGate_single_carrier_alignment_fromEventFlow

instance KKTTasteGate_single_carrier_alignment_ChapterTasteGate :
    ChapterTasteGate KKTUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro packet
    change
      KKTTasteGate_single_carrier_alignment_fromEventFlow
        (KKTTasteGate_single_carrier_alignment_toEventFlow packet) = some packet
    exact KKTTasteGate_single_carrier_alignment_round_trip packet
  layer_separation := by
    intro x y hxy heq
    exact hxy (KKTTasteGate_single_carrier_alignment_toEventFlow_injective heq)

def KKTTasteGate_single_carrier_alignment_taste_gate : ChapterTasteGate KKTUp :=
  -- BEDC touchpoint anchor: BHist BMark
  KKTTasteGate_single_carrier_alignment_ChapterTasteGate

private theorem KKTTasteGate_single_carrier_alignment_semantic_namecert
    (row route provenance : BHist) :
    Cont row route provenance →
      SemanticNameCert
        (fun h : BHist => hsame h provenance)
        (fun h : BHist => hsame h row ∨ hsame h route ∨ hsame h provenance)
        (fun h : BHist => hsame h provenance ∧ Cont row route provenance)
        hsame := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert NameCert
  intro hcont
  refine
    { core :=
        { carrier_inhabited := ?_
          equiv_refl := ?_
          equiv_symm := ?_
          equiv_trans := ?_
          carrier_respects_equiv := ?_ }
      pattern_sound := ?_
      ledger_sound := ?_ }
  · exact ⟨provenance, hsame_refl provenance⟩
  · intro h _source
    exact hsame_refl h
  · intro _h _k same
    exact hsame_symm same
  · intro _h _k _r sameLeft sameRight
    exact hsame_trans sameLeft sameRight
  · intro _h _k same source
    exact hsame_trans (hsame_symm same) source
  · intro h source
    exact Or.inr (Or.inr source)
  · intro h source
    exact And.intro source hcont

theorem KKTTasteGate_single_carrier_alignment :
    Nonempty KKTUp ∧ ChapterTasteGate KKTUp ∧
      (∀ _packet : KKTUp, ∃ row route provenance : BHist,
        Cont row route provenance ∧
          SemanticNameCert
            (fun h : BHist => hsame h provenance)
            (fun h : BHist => hsame h row ∨ hsame h route ∨ hsame h provenance)
            (fun h : BHist => hsame h provenance ∧ Cont row route provenance)
            hsame) := by
  -- BEDC touchpoint anchor: BHist Cont hsame SemanticNameCert ChapterTasteGate
  constructor
  · exact ⟨KKTUp.mk BHist.Empty BHist.Empty⟩
  · constructor
    · exact KKTTasteGate_single_carrier_alignment_ChapterTasteGate
    · intro packet
      cases packet with
      | mk row route =>
          refine ⟨row, route, append row route, ?_, ?_⟩
          · rfl
          · exact KKTTasteGate_single_carrier_alignment_semantic_namecert row route
              (append row route) rfl

end BEDC.Derived.KKTUp
