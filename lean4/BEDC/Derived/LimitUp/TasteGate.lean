import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.LimitUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive LimitUp : Type where
  | mk (stream readback dyadic realSeal transport continuation history provenance name : BHist) :
      LimitUp
  deriving DecidableEq

def limitEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: limitEncodeBHist h
  | BHist.e1 h => BMark.b1 :: limitEncodeBHist h

def limitDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (limitDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (limitDecodeBHist tail)

private theorem limitDecodeEncodeBHist :
    ∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem LimitTasteGate_single_carrier_alignment_decode_aux :
    ∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h :=
  limitDecodeEncodeBHist

private theorem LimitTasteGate_single_carrier_alignment_mk_aux
    {stream stream' readback readback' dyadic dyadic' realSeal realSeal'
      transport transport' continuation continuation' history history' provenance provenance'
      name name' : BHist}
    (hStream : stream' = stream)
    (hReadback : readback' = readback)
    (hDyadic : dyadic' = dyadic)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hContinuation : continuation' = continuation)
    (hHistory : history' = history)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    LimitUp.mk stream' readback' dyadic' realSeal' transport' continuation' history'
        provenance' name' =
      LimitUp.mk stream readback dyadic realSeal transport continuation history provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hStream
  cases hReadback
  cases hDyadic
  cases hRealSeal
  cases hTransport
  cases hContinuation
  cases hHistory
  cases hProvenance
  cases hName
  rfl

def limitFields : LimitUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | LimitUp.mk stream readback dyadic realSeal transport continuation history provenance name =>
      [stream, readback, dyadic, realSeal, transport, continuation, history, provenance, name]

def limitToEventFlow : LimitUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | LimitUp.mk stream readback dyadic realSeal transport continuation history provenance name =>
      [limitEncodeBHist stream,
        limitEncodeBHist readback,
        limitEncodeBHist dyadic,
        limitEncodeBHist realSeal,
        limitEncodeBHist transport,
        limitEncodeBHist continuation,
        limitEncodeBHist history,
        limitEncodeBHist provenance,
        limitEncodeBHist name]

def limitFromEventFlow : EventFlow → Option LimitUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | stream :: restReadback =>
      match restReadback with
      | [] => none
      | readback :: restDyadic =>
          match restDyadic with
          | [] => none
          | dyadic :: restRealSeal =>
              match restRealSeal with
              | [] => none
              | realSeal :: restTransport =>
                  match restTransport with
                  | [] => none
                  | transport :: restContinuation =>
                      match restContinuation with
                      | [] => none
                      | continuation :: restHistory =>
                          match restHistory with
                          | [] => none
                          | history :: restProvenance =>
                              match restProvenance with
                              | [] => none
                              | provenance :: restName =>
                                  match restName with
                                  | [] => none
                                  | name :: rest =>
                                      match rest with
                                      | [] =>
                                          some
                                            (LimitUp.mk
                                              (limitDecodeBHist stream)
                                              (limitDecodeBHist readback)
                                              (limitDecodeBHist dyadic)
                                              (limitDecodeBHist realSeal)
                                              (limitDecodeBHist transport)
                                              (limitDecodeBHist continuation)
                                              (limitDecodeBHist history)
                                              (limitDecodeBHist provenance)
                                              (limitDecodeBHist name))
                                      | _ :: _ => none

private theorem limit_mk_congr
    {stream₁ stream₂ readback₁ readback₂ dyadic₁ dyadic₂ realSeal₁ realSeal₂
      transport₁ transport₂ continuation₁ continuation₂ history₁ history₂
      provenance₁ provenance₂ name₁ name₂ : BHist} :
    stream₁ = stream₂ → readback₁ = readback₂ → dyadic₁ = dyadic₂ →
      realSeal₁ = realSeal₂ → transport₁ = transport₂ →
        continuation₁ = continuation₂ → history₁ = history₂ →
          provenance₁ = provenance₂ → name₁ = name₂ →
            LimitUp.mk stream₁ readback₁ dyadic₁ realSeal₁ transport₁ continuation₁
                history₁ provenance₁ name₁ =
              LimitUp.mk stream₂ readback₂ dyadic₂ realSeal₂ transport₂ continuation₂
                history₂ provenance₂ name₂ := by
  -- BEDC touchpoint anchor: BHist BMark
  intro hstream hreadback hdyadic hrealSeal htransport hcontinuation hhistory hprovenance hname
  cases hstream
  cases hreadback
  cases hdyadic
  cases hrealSeal
  cases htransport
  cases hcontinuation
  cases hhistory
  cases hprovenance
  cases hname
  rfl

private theorem limit_round_trip :
    ∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk stream readback dyadic realSeal transport continuation history provenance name =>
      exact
        congrArg some
          (LimitTasteGate_single_carrier_alignment_mk_aux
            (LimitTasteGate_single_carrier_alignment_decode_aux stream)
            (LimitTasteGate_single_carrier_alignment_decode_aux readback)
            (LimitTasteGate_single_carrier_alignment_decode_aux dyadic)
            (LimitTasteGate_single_carrier_alignment_decode_aux realSeal)
            (LimitTasteGate_single_carrier_alignment_decode_aux transport)
            (LimitTasteGate_single_carrier_alignment_decode_aux continuation)
            (LimitTasteGate_single_carrier_alignment_decode_aux history)
            (LimitTasteGate_single_carrier_alignment_decode_aux provenance)
            (LimitTasteGate_single_carrier_alignment_decode_aux name))

private theorem limitToEventFlow_injective {x y : LimitUp} :
    limitToEventFlow x = limitToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      limitFromEventFlow (limitToEventFlow x) =
        limitFromEventFlow (limitToEventFlow y) :=
    congrArg limitFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (limit_round_trip x).symm (Eq.trans hread (limit_round_trip y)))

private theorem limit_field_faithful :
    ∀ x y : LimitUp, limitFields x = limitFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk stream₁ readback₁ dyadic₁ realSeal₁ transport₁ continuation₁ history₁
      provenance₁ name₁ =>
      cases y with
      | mk stream₂ readback₂ dyadic₂ realSeal₂ transport₂ continuation₂ history₂
          provenance₂ name₂ =>
          injection hfields with hstream tail0
          injection tail0 with hreadback tail1
          injection tail1 with hdyadic tail2
          injection tail2 with hrealSeal tail3
          injection tail3 with htransport tail4
          injection tail4 with hcontinuation tail5
          injection tail5 with hhistory tail6
          injection tail6 with hprovenance tail7
          injection tail7 with hname _
          subst hstream
          subst hreadback
          subst hdyadic
          subst hrealSeal
          subst htransport
          subst hcontinuation
          subst hhistory
          subst hprovenance
          subst hname
          rfl

private theorem LimitTasteGate_single_carrier_alignment_round_trip_aux :
    ∀ x : LimitUp, limitFromEventFlow (limitToEventFlow x) = some x :=
  limit_round_trip

private theorem LimitTasteGate_single_carrier_alignment_injective_aux
    {x y : LimitUp} :
    limitToEventFlow x = limitToEventFlow y → x = y :=
  limitToEventFlow_injective

private theorem LimitTasteGate_single_carrier_alignment_fields_aux :
    ∀ x y : LimitUp, limitFields x = limitFields y → x = y :=
  limit_field_faithful

instance limitBHistCarrier : BHistCarrier LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := limitToEventFlow
  fromEventFlow := limitFromEventFlow

instance limitChapterTasteGate : ChapterTasteGate LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change limitFromEventFlow (limitToEventFlow x) = some x
    exact limit_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (limitToEventFlow_injective heq)

instance limitFieldFaithful : FieldFaithful LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := limitFields
  field_faithful := limit_field_faithful

instance limitNontrivial : Nontrivial LimitUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨LimitUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      LimitUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate LimitUp :=
  -- BEDC touchpoint anchor: BHist BMark
  limitChapterTasteGate

theorem LimitUpTasteGate_single_carrier_alignment :
    (∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h) ∧
      (∀ stream readback dyadic realSeal transport continuation history provenance name : BHist,
        limitFields
            (LimitUp.mk stream readback dyadic realSeal transport continuation history provenance
              name) =
          [stream, readback, dyadic, realSeal, transport, continuation, history, provenance,
            name]) ∧
        limitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark FieldFaithful Nontrivial
  constructor
  · intro h
    induction h with
    | Empty => rfl
    | e0 h ih => exact congrArg BHist.e0 ih
    | e1 h ih => exact congrArg BHist.e1 ih
  · constructor
    · intro stream readback dyadic realSeal transport continuation history provenance name
      rfl
    · rfl

theorem LimitTasteGate_single_carrier_alignment :
    (∀ h : BHist, limitDecodeBHist (limitEncodeBHist h) = h) ∧
      (∀ stream readback dyadic realSeal transport continuation history provenance name : BHist,
        limitFields
            (LimitUp.mk stream readback dyadic realSeal transport continuation history provenance
              name) =
          [stream, readback, dyadic, realSeal, transport, continuation, history, provenance,
            name]) ∧
        limitEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  exact LimitUpTasteGate_single_carrier_alignment

end BEDC.Derived.LimitUp
