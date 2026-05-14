import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CompactNetModulusBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CompactNetModulusBudgetUp : Type where
  | mk :
      (compactNet modulus fold uniform selector transport route provenance name : BHist) →
      CompactNetModulusBudgetUp
  deriving DecidableEq

def compactNetModulusBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: compactNetModulusBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: compactNetModulusBudgetEncodeBHist h

def compactNetModulusBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (compactNetModulusBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (compactNetModulusBudgetDecodeBHist tail)

private theorem compactNetModulusBudgetDecode_encode_bhist :
    ∀ h : BHist,
      compactNetModulusBudgetDecodeBHist (compactNetModulusBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def compactNetModulusBudgetFields :
    CompactNetModulusBudgetUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CompactNetModulusBudgetUp.mk compactNet modulus fold uniform selector transport route
      provenance name =>
      [compactNet, modulus, fold, uniform, selector, transport, route, provenance, name]

def compactNetModulusBudgetToEventFlow :
    CompactNetModulusBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (compactNetModulusBudgetFields x).map compactNetModulusBudgetEncodeBHist

def compactNetModulusBudgetFromEventFlow :
    EventFlow → Option CompactNetModulusBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | compactNet :: rest0 =>
      match rest0 with
      | [] => none
      | modulus :: rest1 =>
          match rest1 with
          | [] => none
          | fold :: rest2 =>
              match rest2 with
              | [] => none
              | uniform :: rest3 =>
                  match rest3 with
                  | [] => none
                  | selector :: rest4 =>
                      match rest4 with
                      | [] => none
                      | transport :: rest5 =>
                          match rest5 with
                          | [] => none
                          | route :: rest6 =>
                              match rest6 with
                              | [] => none
                              | provenance :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | name :: rest8 =>
                                      match rest8 with
                                      | [] =>
                                          some
                                            (CompactNetModulusBudgetUp.mk
                                              (compactNetModulusBudgetDecodeBHist compactNet)
                                              (compactNetModulusBudgetDecodeBHist modulus)
                                              (compactNetModulusBudgetDecodeBHist fold)
                                              (compactNetModulusBudgetDecodeBHist uniform)
                                              (compactNetModulusBudgetDecodeBHist selector)
                                              (compactNetModulusBudgetDecodeBHist transport)
                                              (compactNetModulusBudgetDecodeBHist route)
                                              (compactNetModulusBudgetDecodeBHist provenance)
                                              (compactNetModulusBudgetDecodeBHist name))
                                      | _ :: _ => none

private theorem compactNetModulusBudget_round_trip :
    ∀ x : CompactNetModulusBudgetUp,
      compactNetModulusBudgetFromEventFlow
        (compactNetModulusBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk compactNet modulus fold uniform selector transport route provenance name =>
      change
        some
          (CompactNetModulusBudgetUp.mk
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist compactNet))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist modulus))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist fold))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist uniform))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist selector))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist transport))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist route))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist provenance))
            (compactNetModulusBudgetDecodeBHist
              (compactNetModulusBudgetEncodeBHist name))) =
          some
            (CompactNetModulusBudgetUp.mk compactNet modulus fold uniform selector transport
              route provenance name)
      rw [compactNetModulusBudgetDecode_encode_bhist compactNet,
        compactNetModulusBudgetDecode_encode_bhist modulus,
        compactNetModulusBudgetDecode_encode_bhist fold,
        compactNetModulusBudgetDecode_encode_bhist uniform,
        compactNetModulusBudgetDecode_encode_bhist selector,
        compactNetModulusBudgetDecode_encode_bhist transport,
        compactNetModulusBudgetDecode_encode_bhist route,
        compactNetModulusBudgetDecode_encode_bhist provenance,
        compactNetModulusBudgetDecode_encode_bhist name]

private theorem compactNetModulusBudgetToEventFlow_injective
    {x y : CompactNetModulusBudgetUp} :
    compactNetModulusBudgetToEventFlow x =
      compactNetModulusBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      compactNetModulusBudgetFromEventFlow
          (compactNetModulusBudgetToEventFlow x) =
        compactNetModulusBudgetFromEventFlow
          (compactNetModulusBudgetToEventFlow y) :=
    congrArg compactNetModulusBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (compactNetModulusBudget_round_trip x).symm
      (Eq.trans hread (compactNetModulusBudget_round_trip y)))

instance compactNetModulusBudgetBHistCarrier :
    BHistCarrier CompactNetModulusBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := compactNetModulusBudgetToEventFlow
  fromEventFlow := compactNetModulusBudgetFromEventFlow

instance compactNetModulusBudgetChapterTasteGate :
    ChapterTasteGate CompactNetModulusBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      compactNetModulusBudgetFromEventFlow
        (compactNetModulusBudgetToEventFlow x) = some x
    exact compactNetModulusBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (compactNetModulusBudgetToEventFlow_injective heq)

instance compactNetModulusBudgetFieldFaithful :
    FieldFaithful CompactNetModulusBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := compactNetModulusBudgetFields
  field_faithful := by
    intro x y h
    cases x with
    | mk compactNet₁ modulus₁ fold₁ uniform₁ selector₁ transport₁ route₁ provenance₁ name₁ =>
        cases y with
        | mk compactNet₂ modulus₂ fold₂ uniform₂ selector₂ transport₂ route₂ provenance₂ name₂ =>
            injection h with hCompactNet hRest₁
            injection hRest₁ with hModulus hRest₂
            injection hRest₂ with hFold hRest₃
            injection hRest₃ with hUniform hRest₄
            injection hRest₄ with hSelector hRest₅
            injection hRest₅ with hTransport hRest₆
            injection hRest₆ with hRoute hRest₇
            injection hRest₇ with hProvenance hRest₈
            injection hRest₈ with hName _
            subst hCompactNet
            subst hModulus
            subst hFold
            subst hUniform
            subst hSelector
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl

instance compactNetModulusBudgetNontrivial :
    Nontrivial CompactNetModulusBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨CompactNetModulusBudgetUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      CompactNetModulusBudgetUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

theorem CompactNetModulusBudgetTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier CompactNetModulusBudgetUp) ∧
      Nonempty (ChapterTasteGate CompactNetModulusBudgetUp) ∧
        Nonempty (FieldFaithful CompactNetModulusBudgetUp) ∧
          Nonempty (Nontrivial CompactNetModulusBudgetUp) ∧
            compactNetModulusBudgetEncodeBHist BHist.Empty = ([] : RawEvent) ∧
              compactNetModulusBudgetEncodeBHist (BHist.e0 BHist.Empty) = [BMark.b0] := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact ⟨compactNetModulusBudgetBHistCarrier⟩
  · constructor
    · exact ⟨compactNetModulusBudgetChapterTasteGate⟩
    · constructor
      · exact ⟨compactNetModulusBudgetFieldFaithful⟩
      · constructor
        · exact ⟨compactNetModulusBudgetNontrivial⟩
        · constructor
          · rfl
          · rfl

end BEDC.Derived.CompactNetModulusBudgetUp
