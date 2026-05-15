import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalRealRequestReuseUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalRealRequestReuseUp : Type where
  | mk
      (requestBundle selector window readback dyadicLedger realSeal transport replay provenance
        name : BHist) :
      CofinalRealRequestReuseUp
  deriving DecidableEq

def cofinalRealRequestReuseFields : CofinalRealRequestReuseUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalRealRequestReuseUp.mk requestBundle selector window readback dyadicLedger realSeal
      transport replay provenance name =>
      [requestBundle, selector, window, readback, dyadicLedger, realSeal, transport, replay,
        provenance, name]

def cofinalRealRequestReuseEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalRealRequestReuseEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalRealRequestReuseEncodeBHist h

def cofinalRealRequestReuseDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalRealRequestReuseDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalRealRequestReuseDecodeBHist tail)

private theorem cofinalRealRequestReuseDecode_encode_bhist :
    ∀ h : BHist,
      cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cofinalRealRequestReuse_mk_congr
    {requestBundle requestBundle' selector selector' window window' readback readback'
      dyadicLedger dyadicLedger' realSeal realSeal' transport transport' replay replay' provenance
      provenance' name name' : BHist}
    (hRequestBundle : requestBundle' = requestBundle)
    (hSelector : selector' = selector)
    (hWindow : window' = window)
    (hReadback : readback' = readback)
    (hDyadicLedger : dyadicLedger' = dyadicLedger)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hReplay : replay' = replay)
    (hProvenance : provenance' = provenance)
    (hName : name' = name) :
    CofinalRealRequestReuseUp.mk requestBundle' selector' window' readback' dyadicLedger'
        realSeal' transport' replay' provenance' name' =
      CofinalRealRequestReuseUp.mk requestBundle selector window readback dyadicLedger realSeal
        transport replay provenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hRequestBundle
  cases hSelector
  cases hWindow
  cases hReadback
  cases hDyadicLedger
  cases hRealSeal
  cases hTransport
  cases hReplay
  cases hProvenance
  cases hName
  rfl

def cofinalRealRequestReuseToEventFlow : CofinalRealRequestReuseUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | CofinalRealRequestReuseUp.mk requestBundle selector window readback dyadicLedger realSeal
      transport replay provenance name =>
      [[BMark.b0],
        cofinalRealRequestReuseEncodeBHist requestBundle,
        [BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist selector,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist window,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist readback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalRealRequestReuseEncodeBHist replay,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cofinalRealRequestReuseEncodeBHist name]

private def cofinalRealRequestReuseEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cofinalRealRequestReuseEventAtDefault index rest

def cofinalRealRequestReuseFromEventFlow (ef : EventFlow) :
    Option CofinalRealRequestReuseUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CofinalRealRequestReuseUp.mk
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 1 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 3 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 5 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 7 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 9 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 11 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 13 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 15 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 17 ef))
      (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEventAtDefault 19 ef)))

private theorem cofinalRealRequestReuse_round_trip :
    ∀ x : CofinalRealRequestReuseUp,
      cofinalRealRequestReuseFromEventFlow (cofinalRealRequestReuseToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk requestBundle selector window readback dyadicLedger realSeal transport replay provenance name =>
      change
        some
          (CofinalRealRequestReuseUp.mk
            (cofinalRealRequestReuseDecodeBHist
              (cofinalRealRequestReuseEncodeBHist requestBundle))
            (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEncodeBHist selector))
            (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEncodeBHist window))
            (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEncodeBHist readback))
            (cofinalRealRequestReuseDecodeBHist
              (cofinalRealRequestReuseEncodeBHist dyadicLedger))
            (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEncodeBHist realSeal))
            (cofinalRealRequestReuseDecodeBHist
              (cofinalRealRequestReuseEncodeBHist transport))
            (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEncodeBHist replay))
            (cofinalRealRequestReuseDecodeBHist
              (cofinalRealRequestReuseEncodeBHist provenance))
            (cofinalRealRequestReuseDecodeBHist (cofinalRealRequestReuseEncodeBHist name))) =
          some
            (CofinalRealRequestReuseUp.mk requestBundle selector window readback dyadicLedger
              realSeal transport replay provenance name)
      exact
        congrArg some
          (cofinalRealRequestReuse_mk_congr
            (cofinalRealRequestReuseDecode_encode_bhist requestBundle)
            (cofinalRealRequestReuseDecode_encode_bhist selector)
            (cofinalRealRequestReuseDecode_encode_bhist window)
            (cofinalRealRequestReuseDecode_encode_bhist readback)
            (cofinalRealRequestReuseDecode_encode_bhist dyadicLedger)
            (cofinalRealRequestReuseDecode_encode_bhist realSeal)
            (cofinalRealRequestReuseDecode_encode_bhist transport)
            (cofinalRealRequestReuseDecode_encode_bhist replay)
            (cofinalRealRequestReuseDecode_encode_bhist provenance)
            (cofinalRealRequestReuseDecode_encode_bhist name))

private theorem cofinalRealRequestReuseToEventFlow_injective
    {x y : CofinalRealRequestReuseUp} :
    cofinalRealRequestReuseToEventFlow x = cofinalRealRequestReuseToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cofinalRealRequestReuseFromEventFlow (cofinalRealRequestReuseToEventFlow x) =
        cofinalRealRequestReuseFromEventFlow (cofinalRealRequestReuseToEventFlow y) :=
    congrArg cofinalRealRequestReuseFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalRealRequestReuse_round_trip x).symm
      (Eq.trans hread (cofinalRealRequestReuse_round_trip y)))

instance cofinalRealRequestReuseBHistCarrier : BHistCarrier CofinalRealRequestReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cofinalRealRequestReuseToEventFlow
  fromEventFlow := cofinalRealRequestReuseFromEventFlow

instance cofinalRealRequestReuseChapterTasteGate :
    ChapterTasteGate CofinalRealRequestReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change cofinalRealRequestReuseFromEventFlow (cofinalRealRequestReuseToEventFlow x) = some x
    exact cofinalRealRequestReuse_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalRealRequestReuseToEventFlow_injective heq)

instance cofinalRealRequestReuseFieldFaithful : FieldFaithful CofinalRealRequestReuseUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := cofinalRealRequestReuseFields
  field_faithful := by
    intro x y h
    cases x with
    | mk requestBundle₁ selector₁ window₁ readback₁ dyadicLedger₁ realSeal₁ transport₁
        replay₁ provenance₁ name₁ =>
        cases y with
        | mk requestBundle₂ selector₂ window₂ readback₂ dyadicLedger₂ realSeal₂ transport₂
            replay₂ provenance₂ name₂ =>
            injection h with hRequestBundle hRest₁
            injection hRest₁ with hSelector hRest₂
            injection hRest₂ with hWindow hRest₃
            injection hRest₃ with hReadback hRest₄
            injection hRest₄ with hDyadicLedger hRest₅
            injection hRest₅ with hRealSeal hRest₆
            injection hRest₆ with hTransport hRest₇
            injection hRest₇ with hReplay hRest₈
            injection hRest₈ with hProvenance hRest₉
            injection hRest₉ with hName _
            cases hRequestBundle
            cases hSelector
            cases hWindow
            cases hReadback
            cases hDyadicLedger
            cases hRealSeal
            cases hTransport
            cases hReplay
            cases hProvenance
            cases hName
            rfl

theorem CofinalRealRequestReuseTasteGate_single_carrier_alignment :
    (∃ packet : CofinalRealRequestReuseUp,
        BHistCarrier.fromEventFlow (BHistCarrier.toEventFlow packet) = some packet ∧
          List.Mem BHist.Empty (cofinalRealRequestReuseFields packet)) ∧
      Nonempty (ChapterTasteGate CofinalRealRequestReuseUp) ∧
        Nonempty (FieldFaithful CofinalRealRequestReuseUp) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · refine
      ⟨CofinalRealRequestReuseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty, ?_, ?_⟩
    · change
        cofinalRealRequestReuseFromEventFlow
            (cofinalRealRequestReuseToEventFlow
              (CofinalRealRequestReuseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
                BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)) =
          some
            (CofinalRealRequestReuseUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty)
      exact cofinalRealRequestReuse_round_trip _
    · exact List.Mem.head _
  · constructor
    · exact ⟨cofinalRealRequestReuseChapterTasteGate⟩
    · exact ⟨cofinalRealRequestReuseFieldFaithful⟩

end BEDC.Derived.CofinalRealRequestReuseUp
