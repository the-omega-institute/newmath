import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CofinalModulusNormalizationSealUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive CofinalModulusNormalizationSealUp : Type where
  | mk :
      (leftSchedule rightSchedule modulusSeal sharedWindow dyadicLedger regseqReadback realSeal
        transport routes provenance handoffLedger nameCert : BHist) →
      CofinalModulusNormalizationSealUp
  deriving DecidableEq

def cofinalModulusNormalizationSealFields :
    CofinalModulusNormalizationSealUp → List BHist
  | CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal sharedWindow
      dyadicLedger regseqReadback realSeal transport routes provenance handoffLedger nameCert =>
      [leftSchedule, rightSchedule, modulusSeal, sharedWindow, dyadicLedger, regseqReadback,
        realSeal, transport, routes, provenance, handoffLedger, nameCert]

def cofinalModulusNormalizationSealEncodeBHist : BHist → RawEvent
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cofinalModulusNormalizationSealEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cofinalModulusNormalizationSealEncodeBHist h

def cofinalModulusNormalizationSealDecodeBHist : RawEvent → BHist
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cofinalModulusNormalizationSealDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cofinalModulusNormalizationSealDecodeBHist tail)

private theorem cofinalModulusNormalizationSeal_decode_encode_bhist :
    ∀ h : BHist,
      cofinalModulusNormalizationSealDecodeBHist
          (cofinalModulusNormalizationSealEncodeBHist h) =
        h := by
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private theorem cofinalModulusNormalizationSeal_mk_congr
    {leftSchedule leftSchedule' rightSchedule rightSchedule' modulusSeal modulusSeal'
      sharedWindow sharedWindow' dyadicLedger dyadicLedger' regseqReadback regseqReadback'
      realSeal realSeal' transport transport' routes routes' provenance provenance'
      handoffLedger handoffLedger' nameCert nameCert' : BHist}
    (hLeftSchedule : leftSchedule' = leftSchedule)
    (hRightSchedule : rightSchedule' = rightSchedule)
    (hModulusSeal : modulusSeal' = modulusSeal)
    (hSharedWindow : sharedWindow' = sharedWindow)
    (hDyadicLedger : dyadicLedger' = dyadicLedger)
    (hRegseqReadback : regseqReadback' = regseqReadback)
    (hRealSeal : realSeal' = realSeal)
    (hTransport : transport' = transport)
    (hRoutes : routes' = routes)
    (hProvenance : provenance' = provenance)
    (hHandoffLedger : handoffLedger' = handoffLedger)
    (hNameCert : nameCert' = nameCert) :
    CofinalModulusNormalizationSealUp.mk leftSchedule' rightSchedule' modulusSeal'
        sharedWindow' dyadicLedger' regseqReadback' realSeal' transport' routes'
        provenance' handoffLedger' nameCert' =
      CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal
        sharedWindow dyadicLedger regseqReadback realSeal transport routes provenance
        handoffLedger nameCert := by
  cases hLeftSchedule
  cases hRightSchedule
  cases hModulusSeal
  cases hSharedWindow
  cases hDyadicLedger
  cases hRegseqReadback
  cases hRealSeal
  cases hTransport
  cases hRoutes
  cases hProvenance
  cases hHandoffLedger
  cases hNameCert
  rfl

def cofinalModulusNormalizationSealToEventFlow :
    CofinalModulusNormalizationSealUp → EventFlow
  | CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal sharedWindow
      dyadicLedger regseqReadback realSeal transport routes provenance handoffLedger nameCert =>
      [[BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist leftSchedule,
        [BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist rightSchedule,
        [BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist modulusSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist sharedWindow,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist dyadicLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist regseqReadback,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist realSeal,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist transport,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist routes,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist provenance,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist handoffLedger,
        [BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b1,
          BMark.b1, BMark.b1, BMark.b1, BMark.b1, BMark.b0],
        cofinalModulusNormalizationSealEncodeBHist nameCert]

private def cofinalModulusNormalizationSealEventAtDefault :
    Nat → EventFlow → RawEvent
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      cofinalModulusNormalizationSealEventAtDefault index rest

def cofinalModulusNormalizationSealFromEventFlow
    (ef : EventFlow) : Option CofinalModulusNormalizationSealUp :=
  some
    (CofinalModulusNormalizationSealUp.mk
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 1 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 3 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 5 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 7 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 9 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 11 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 13 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 15 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 17 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 19 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 21 ef))
      (cofinalModulusNormalizationSealDecodeBHist
        (cofinalModulusNormalizationSealEventAtDefault 23 ef)))

private theorem cofinalModulusNormalizationSeal_round_trip :
    ∀ x : CofinalModulusNormalizationSealUp,
      cofinalModulusNormalizationSealFromEventFlow
          (cofinalModulusNormalizationSealToEventFlow x) =
        some x := by
  intro x
  cases x with
  | mk leftSchedule rightSchedule modulusSeal sharedWindow dyadicLedger regseqReadback
      realSeal transport routes provenance handoffLedger nameCert =>
      change
        some
            (CofinalModulusNormalizationSealUp.mk
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist leftSchedule))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist rightSchedule))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist modulusSeal))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist sharedWindow))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist dyadicLedger))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist regseqReadback))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist realSeal))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist transport))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist routes))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist provenance))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist handoffLedger))
              (cofinalModulusNormalizationSealDecodeBHist
                (cofinalModulusNormalizationSealEncodeBHist nameCert))) =
          some
            (CofinalModulusNormalizationSealUp.mk leftSchedule rightSchedule modulusSeal
              sharedWindow dyadicLedger regseqReadback realSeal transport routes provenance
              handoffLedger nameCert)
      exact
        congrArg some
          (cofinalModulusNormalizationSeal_mk_congr
            (cofinalModulusNormalizationSeal_decode_encode_bhist leftSchedule)
            (cofinalModulusNormalizationSeal_decode_encode_bhist rightSchedule)
            (cofinalModulusNormalizationSeal_decode_encode_bhist modulusSeal)
            (cofinalModulusNormalizationSeal_decode_encode_bhist sharedWindow)
            (cofinalModulusNormalizationSeal_decode_encode_bhist dyadicLedger)
            (cofinalModulusNormalizationSeal_decode_encode_bhist regseqReadback)
            (cofinalModulusNormalizationSeal_decode_encode_bhist realSeal)
            (cofinalModulusNormalizationSeal_decode_encode_bhist transport)
            (cofinalModulusNormalizationSeal_decode_encode_bhist routes)
            (cofinalModulusNormalizationSeal_decode_encode_bhist provenance)
            (cofinalModulusNormalizationSeal_decode_encode_bhist handoffLedger)
            (cofinalModulusNormalizationSeal_decode_encode_bhist nameCert))

private theorem cofinalModulusNormalizationSealToEventFlow_injective
    {x y : CofinalModulusNormalizationSealUp} :
    cofinalModulusNormalizationSealToEventFlow x =
      cofinalModulusNormalizationSealToEventFlow y →
        x = y := by
  intro heq
  have hread :
      cofinalModulusNormalizationSealFromEventFlow
          (cofinalModulusNormalizationSealToEventFlow x) =
        cofinalModulusNormalizationSealFromEventFlow
          (cofinalModulusNormalizationSealToEventFlow y) :=
    congrArg cofinalModulusNormalizationSealFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (cofinalModulusNormalizationSeal_round_trip x).symm
      (Eq.trans hread (cofinalModulusNormalizationSeal_round_trip y)))

instance cofinalModulusNormalizationSealBHistCarrier :
    BHistCarrier CofinalModulusNormalizationSealUp where
  toEventFlow := cofinalModulusNormalizationSealToEventFlow
  fromEventFlow := cofinalModulusNormalizationSealFromEventFlow

instance cofinalModulusNormalizationSealChapterTasteGate :
    ChapterTasteGate CofinalModulusNormalizationSealUp where
  round_trip := by
    intro x
    exact cofinalModulusNormalizationSeal_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (cofinalModulusNormalizationSealToEventFlow_injective heq)

instance cofinalModulusNormalizationSealFieldFaithful :
    FieldFaithful CofinalModulusNormalizationSealUp where
  fields := cofinalModulusNormalizationSealFields
  field_faithful := by
    intro x y h
    cases x with
    | mk leftSchedule₁ rightSchedule₁ modulusSeal₁ sharedWindow₁ dyadicLedger₁
        regseqReadback₁ realSeal₁ transport₁ routes₁ provenance₁ handoffLedger₁ nameCert₁ =>
        cases y with
        | mk leftSchedule₂ rightSchedule₂ modulusSeal₂ sharedWindow₂ dyadicLedger₂
            regseqReadback₂ realSeal₂ transport₂ routes₂ provenance₂ handoffLedger₂ nameCert₂ =>
            injection h with hLeftSchedule hRest₁
            injection hRest₁ with hRightSchedule hRest₂
            injection hRest₂ with hModulusSeal hRest₃
            injection hRest₃ with hSharedWindow hRest₄
            injection hRest₄ with hDyadicLedger hRest₅
            injection hRest₅ with hRegseqReadback hRest₆
            injection hRest₆ with hRealSeal hRest₇
            injection hRest₇ with hTransport hRest₈
            injection hRest₈ with hRoutes hRest₉
            injection hRest₉ with hProvenance hRest₁₀
            injection hRest₁₀ with hHandoffLedger hRest₁₁
            injection hRest₁₁ with hNameCert _
            cases hLeftSchedule
            cases hRightSchedule
            cases hModulusSeal
            cases hSharedWindow
            cases hDyadicLedger
            cases hRegseqReadback
            cases hRealSeal
            cases hTransport
            cases hRoutes
            cases hProvenance
            cases hHandoffLedger
            cases hNameCert
            rfl

instance cofinalModulusNormalizationSealNontrivial :
    Nontrivial CofinalModulusNormalizationSealUp where
  witness_pair := by
    refine
      ⟨CofinalModulusNormalizationSealUp.mk BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty,
        CofinalModulusNormalizationSealUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
          BHist.Empty BHist.Empty BHist.Empty, ?_⟩
    intro h
    cases h

theorem CofinalModulusNormalizationSealTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CofinalModulusNormalizationSealUp) ∧
      Nonempty (FieldFaithful CofinalModulusNormalizationSealUp) ∧
        Nonempty (Nontrivial CofinalModulusNormalizationSealUp) := by
  constructor
  · exact ⟨cofinalModulusNormalizationSealChapterTasteGate⟩
  · constructor
    · exact ⟨cofinalModulusNormalizationSealFieldFaithful⟩
    · exact ⟨cofinalModulusNormalizationSealNontrivial⟩

end BEDC.Derived.CofinalModulusNormalizationSealUp
