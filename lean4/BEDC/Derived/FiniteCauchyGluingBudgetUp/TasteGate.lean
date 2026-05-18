import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.FiniteCauchyGluingBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive FiniteCauchyGluingBudgetUp : Type where
  | mk
      (left right bridge budget gluing seam transport replay provenance localName : BHist) :
      FiniteCauchyGluingBudgetUp
  deriving DecidableEq

def finiteCauchyGluingBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCauchyGluingBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCauchyGluingBudgetEncodeBHist h

def finiteCauchyGluingBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCauchyGluingBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCauchyGluingBudgetDecodeBHist tail)

private theorem finiteCauchyGluingBudgetDecode_encode_bhist :
    ∀ h : BHist,
      finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def finiteCauchyGluingBudgetFields : FiniteCauchyGluingBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCauchyGluingBudgetUp.mk left right bridge budget gluing seam transport replay
      provenance localName =>
      [left, right, bridge, budget, gluing, seam, transport, replay, provenance, localName]

def finiteCauchyGluingBudgetToEventFlow : FiniteCauchyGluingBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (finiteCauchyGluingBudgetFields x).map finiteCauchyGluingBudgetEncodeBHist

def finiteCauchyGluingBudgetFromEventFlow : EventFlow → Option FiniteCauchyGluingBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | left :: rest0 =>
      match rest0 with
      | [] => none
      | right :: rest1 =>
          match rest1 with
          | [] => none
          | bridge :: rest2 =>
              match rest2 with
              | [] => none
              | budget :: rest3 =>
                  match rest3 with
                  | [] => none
                  | gluing :: rest4 =>
                      match rest4 with
                      | [] => none
                      | seam :: rest5 =>
                          match rest5 with
                          | [] => none
                          | transport :: rest6 =>
                              match rest6 with
                              | [] => none
                              | replay :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | provenance :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | localName :: rest9 =>
                                          match rest9 with
                                          | [] =>
                                              some
                                                (FiniteCauchyGluingBudgetUp.mk
                                                  (finiteCauchyGluingBudgetDecodeBHist left)
                                                  (finiteCauchyGluingBudgetDecodeBHist right)
                                                  (finiteCauchyGluingBudgetDecodeBHist bridge)
                                                  (finiteCauchyGluingBudgetDecodeBHist budget)
                                                  (finiteCauchyGluingBudgetDecodeBHist gluing)
                                                  (finiteCauchyGluingBudgetDecodeBHist seam)
                                                  (finiteCauchyGluingBudgetDecodeBHist transport)
                                                  (finiteCauchyGluingBudgetDecodeBHist replay)
                                                  (finiteCauchyGluingBudgetDecodeBHist provenance)
                                                  (finiteCauchyGluingBudgetDecodeBHist localName))
                                          | _ :: _ => none

private theorem finiteCauchyGluingBudget_round_trip :
    ∀ x : FiniteCauchyGluingBudgetUp,
      finiteCauchyGluingBudgetFromEventFlow (finiteCauchyGluingBudgetToEventFlow x) =
        some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk left right bridge budget gluing seam transport replay provenance localName =>
      change
        some
          (FiniteCauchyGluingBudgetUp.mk
            (finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist left))
            (finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist right))
            (finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist bridge))
            (finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist budget))
            (finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist gluing))
            (finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist seam))
            (finiteCauchyGluingBudgetDecodeBHist
              (finiteCauchyGluingBudgetEncodeBHist transport))
            (finiteCauchyGluingBudgetDecodeBHist (finiteCauchyGluingBudgetEncodeBHist replay))
            (finiteCauchyGluingBudgetDecodeBHist
              (finiteCauchyGluingBudgetEncodeBHist provenance))
            (finiteCauchyGluingBudgetDecodeBHist
              (finiteCauchyGluingBudgetEncodeBHist localName))) =
          some
            (FiniteCauchyGluingBudgetUp.mk left right bridge budget gluing seam transport
              replay provenance localName)
      rw [finiteCauchyGluingBudgetDecode_encode_bhist left,
        finiteCauchyGluingBudgetDecode_encode_bhist right,
        finiteCauchyGluingBudgetDecode_encode_bhist bridge,
        finiteCauchyGluingBudgetDecode_encode_bhist budget,
        finiteCauchyGluingBudgetDecode_encode_bhist gluing,
        finiteCauchyGluingBudgetDecode_encode_bhist seam,
        finiteCauchyGluingBudgetDecode_encode_bhist transport,
        finiteCauchyGluingBudgetDecode_encode_bhist replay,
        finiteCauchyGluingBudgetDecode_encode_bhist provenance,
        finiteCauchyGluingBudgetDecode_encode_bhist localName]

private theorem finiteCauchyGluingBudgetToEventFlow_injective
    {x y : FiniteCauchyGluingBudgetUp} :
    finiteCauchyGluingBudgetToEventFlow x = finiteCauchyGluingBudgetToEventFlow y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCauchyGluingBudgetFromEventFlow (finiteCauchyGluingBudgetToEventFlow x) =
        finiteCauchyGluingBudgetFromEventFlow (finiteCauchyGluingBudgetToEventFlow y) :=
    congrArg finiteCauchyGluingBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteCauchyGluingBudget_round_trip x).symm
      (Eq.trans hread (finiteCauchyGluingBudget_round_trip y)))

private theorem finiteCauchyGluingBudget_fields_faithful :
    ∀ x y : FiniteCauchyGluingBudgetUp,
      finiteCauchyGluingBudgetFields x = finiteCauchyGluingBudgetFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk left₁ right₁ bridge₁ budget₁ gluing₁ seam₁ transport₁ replay₁ provenance₁
      localName₁ =>
      cases y with
      | mk left₂ right₂ bridge₂ budget₂ gluing₂ seam₂ transport₂ replay₂ provenance₂
          localName₂ =>
          cases hfields
          rfl

instance finiteCauchyGluingBudgetBHistCarrier :
    BHistCarrier FiniteCauchyGluingBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCauchyGluingBudgetToEventFlow
  fromEventFlow := finiteCauchyGluingBudgetFromEventFlow

instance finiteCauchyGluingBudgetChapterTasteGate :
    ChapterTasteGate FiniteCauchyGluingBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteCauchyGluingBudgetFromEventFlow (finiteCauchyGluingBudgetToEventFlow x) =
        some x
    exact finiteCauchyGluingBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteCauchyGluingBudgetToEventFlow_injective heq)

instance finiteCauchyGluingBudgetFieldFaithful :
    FieldFaithful FiniteCauchyGluingBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := finiteCauchyGluingBudgetFields
  field_faithful := finiteCauchyGluingBudget_fields_faithful

instance finiteCauchyGluingBudgetNontrivial : Nontrivial FiniteCauchyGluingBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨FiniteCauchyGluingBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      FiniteCauchyGluingBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate FiniteCauchyGluingBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  finiteCauchyGluingBudgetChapterTasteGate

namespace TasteGate

theorem FiniteCauchyGluingBudgetObligationSurface
    {left right bridge budget gluing seam transport replay provenance localName : BHist} :
    finiteCauchyGluingBudgetFields
        (FiniteCauchyGluingBudgetUp.mk left right bridge budget gluing seam transport replay
          provenance localName) =
        [left, right, bridge, budget, gluing, seam, transport, replay, provenance,
          localName] ∧
      finiteCauchyGluingBudgetDecodeBHist
          (finiteCauchyGluingBudgetEncodeBHist localName) =
        localName ∧
        Nonempty (ChapterTasteGate FiniteCauchyGluingBudgetUp) ∧
          finiteCauchyGluingBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful Nontrivial
  constructor
  · rfl
  · constructor
    · exact finiteCauchyGluingBudgetDecode_encode_bhist localName
    · constructor
      · exact ⟨finiteCauchyGluingBudgetChapterTasteGate⟩
      · rfl

def taste_gate : ChapterTasteGate FiniteCauchyGluingBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  BEDC.Derived.FiniteCauchyGluingBudgetUp.taste_gate

end TasteGate

end BEDC.Derived.FiniteCauchyGluingBudgetUp
