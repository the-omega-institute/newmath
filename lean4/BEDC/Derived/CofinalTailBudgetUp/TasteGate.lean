import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalTailBudgetUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalTailBudgetUp : Type where
  | mk :
      (modulusBudget tailWindows regSeqHandoff realSeal transport route provenance name :
        BHist) →
      CofinalTailBudgetUp
  deriving DecidableEq

def cofinalTailBudgetEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalTailBudgetEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalTailBudgetEncodeBHist h

def cofinalTailBudgetDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalTailBudgetDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalTailBudgetDecodeBHist tail)

private theorem cofinalTailBudgetDecode_encode_bhist :
    ∀ h : BHist,
      cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem cofinalTailBudget_mk_congr
    {modulusBudget modulusBudget' tailWindows tailWindows' regSeqHandoff
      regSeqHandoff' realSeal realSeal' transport transport' route route'
      provenance provenance' name name' : BHist}
    (hModulus : modulusBudget' = modulusBudget)
    (hTail : tailWindows' = tailWindows)
    (hRegSeq : regSeqHandoff' = regSeqHandoff)
    (hSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hRoute : route' = route)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CofinalTailBudgetUp.mk modulusBudget' tailWindows' regSeqHandoff' realSeal'
        transport' route' provenance' name' =
      CofinalTailBudgetUp.mk modulusBudget tailWindows regSeqHandoff realSeal
        transport route provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hModulus
  cases hTail
  cases hRegSeq
  cases hSeal
  cases hTransport
  cases hRoute
  cases hProvenance
  cases hName
  rfl

def cofinalTailBudgetToEventFlow : CofinalTailBudgetUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalTailBudgetUp.mk modulusBudget tailWindows regSeqHandoff realSeal
      transport route provenance name =>
      [[BMark.b0],
        cofinalTailBudgetEncodeBHist modulusBudget,
        [BMark.b1, BMark.b0],
        cofinalTailBudgetEncodeBHist tailWindows,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalTailBudgetEncodeBHist regSeqHandoff,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalTailBudgetEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalTailBudgetEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalTailBudgetEncodeBHist route,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalTailBudgetEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalTailBudgetEncodeBHist name]

def cofinalTailBudgetFromEventFlow : EventFlow → Option CofinalTailBudgetUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _tag0 :: rest0 =>
      match rest0 with
      | [] => none
      | modulusBudget :: rest1 =>
          match rest1 with
          | [] => none
          | _tag1 :: rest2 =>
              match rest2 with
              | [] => none
              | tailWindows :: rest3 =>
                  match rest3 with
                  | [] => none
                  | _tag2 :: rest4 =>
                      match rest4 with
                      | [] => none
                      | regSeqHandoff :: rest5 =>
                          match rest5 with
                          | [] => none
                          | _tag3 :: rest6 =>
                              match rest6 with
                              | [] => none
                              | realSeal :: rest7 =>
                                  match rest7 with
                                  | [] => none
                                  | _tag4 :: rest8 =>
                                      match rest8 with
                                      | [] => none
                                      | transport :: rest9 =>
                                          match rest9 with
                                          | [] => none
                                          | _tag5 :: rest10 =>
                                              match rest10 with
                                              | [] => none
                                              | route :: rest11 =>
                                                  match rest11 with
                                                  | [] => none
                                                  | _tag6 :: rest12 =>
                                                      match rest12 with
                                                      | [] => none
                                                      | provenance :: rest13 =>
                                                          match rest13 with
                                                          | [] => none
                                                          | _tag7 :: rest14 =>
                                                              match rest14 with
                                                              | [] => none
                                                              | name :: rest15 =>
                                                                  match rest15 with
                                                                  | [] =>
                                                                      some
                                                                        (CofinalTailBudgetUp.mk
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            modulusBudget)
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            tailWindows)
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            regSeqHandoff)
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            realSeal)
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            transport)
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            route)
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            provenance)
                                                                          (cofinalTailBudgetDecodeBHist
                                                                            name))
                                                                  | _ :: _ => none

private theorem cofinalTailBudget_round_trip :
    ∀ x : CofinalTailBudgetUp,
      cofinalTailBudgetFromEventFlow (cofinalTailBudgetToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk modulusBudget tailWindows regSeqHandoff realSeal transport route provenance name =>
      change
        some
          (CofinalTailBudgetUp.mk
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist modulusBudget))
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist tailWindows))
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist regSeqHandoff))
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist realSeal))
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist transport))
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist route))
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist provenance))
            (cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist name))) =
          some
            (CofinalTailBudgetUp.mk modulusBudget tailWindows regSeqHandoff realSeal
              transport route provenance name)
      exact
        congrArg some
          (cofinalTailBudget_mk_congr
            (cofinalTailBudgetDecode_encode_bhist modulusBudget)
            (cofinalTailBudgetDecode_encode_bhist tailWindows)
            (cofinalTailBudgetDecode_encode_bhist regSeqHandoff)
            (cofinalTailBudgetDecode_encode_bhist realSeal)
            (cofinalTailBudgetDecode_encode_bhist transport)
            (cofinalTailBudgetDecode_encode_bhist route)
            (cofinalTailBudgetDecode_encode_bhist provenance)
            (cofinalTailBudgetDecode_encode_bhist name))

private theorem cofinalTailBudgetToEventFlow_injective {x y : CofinalTailBudgetUp} :
    cofinalTailBudgetToEventFlow x = cofinalTailBudgetToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalTailBudgetFromEventFlow (cofinalTailBudgetToEventFlow x) =
        cofinalTailBudgetFromEventFlow (cofinalTailBudgetToEventFlow y) :=
    congrArg cofinalTailBudgetFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalTailBudget_round_trip x).symm
      (Eq.trans hread (cofinalTailBudget_round_trip y)))

instance cofinalTailBudgetBHistCarrier : BHistCarrier CofinalTailBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalTailBudgetToEventFlow
  fromEventFlow := cofinalTailBudgetFromEventFlow

instance cofinalTailBudgetChapterTasteGate : ChapterTasteGate CofinalTailBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalTailBudgetFromEventFlow (cofinalTailBudgetToEventFlow x) = some x
    exact cofinalTailBudget_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalTailBudgetToEventFlow_injective heq)

def taste_gate : ChapterTasteGate CofinalTailBudgetUp :=
  -- BEDC touchpoint anchor: BHist BMark
  cofinalTailBudgetChapterTasteGate

instance cofinalTailBudgetFieldFaithful : FieldFaithful CofinalTailBudgetUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := fun x =>
    match x with
    | CofinalTailBudgetUp.mk modulusBudget tailWindows regSeqHandoff realSeal
        transport route provenance name =>
        [modulusBudget, tailWindows, regSeqHandoff, realSeal, transport, route,
          provenance, name]
  field_faithful := by
    intro x y h
    cases x with
    | mk modulusBudget₁ tailWindows₁ regSeqHandoff₁ realSeal₁ transport₁ route₁
        provenance₁ name₁ =>
        cases y with
        | mk modulusBudget₂ tailWindows₂ regSeqHandoff₂ realSeal₂ transport₂ route₂
            provenance₂ name₂ =>
            simp only [] at h
            injection h with hModulus hRest₁
            injection hRest₁ with hTail hRest₂
            injection hRest₂ with hRegSeq hRest₃
            injection hRest₃ with hSeal hRest₄
            injection hRest₄ with hTransport hRest₅
            injection hRest₅ with hRoute hRest₆
            injection hRest₆ with hProvenance hRest₇
            injection hRest₇ with hName _
            subst hModulus
            subst hTail
            subst hRegSeq
            subst hSeal
            subst hTransport
            subst hRoute
            subst hProvenance
            subst hName
            rfl

theorem CofinalTailBudgetTasteGate_single_carrier_alignment :
    (∀ h : BHist, cofinalTailBudgetDecodeBHist (cofinalTailBudgetEncodeBHist h) = h) ∧
      (∀ x : CofinalTailBudgetUp,
        cofinalTailBudgetFromEventFlow (cofinalTailBudgetToEventFlow x) = some x) ∧
        (∀ x y : CofinalTailBudgetUp,
          cofinalTailBudgetToEventFlow x = cofinalTailBudgetToEventFlow y → x = y) ∧
          cofinalTailBudgetEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact cofinalTailBudgetDecode_encode_bhist
  · constructor
    · exact cofinalTailBudget_round_trip
    · constructor
      · intro x y heq
        exact cofinalTailBudgetToEventFlow_injective heq
      · rfl

end BEDC.Derived.CofinalTailBudgetUp
