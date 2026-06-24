import BEDC.Derived.FiniteCauchyTailHandoffUp
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

def finiteCauchyTailHandoffEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: finiteCauchyTailHandoffEncodeBHist h
  | BHist.e1 h => BMark.b1 :: finiteCauchyTailHandoffEncodeBHist h

def finiteCauchyTailHandoffDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (finiteCauchyTailHandoffDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (finiteCauchyTailHandoffDecodeBHist tail)

private theorem finiteCauchyTailHandoff_decode_encode_bhist :
    ∀ h : BHist,
      finiteCauchyTailHandoffDecodeBHist (finiteCauchyTailHandoffEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def finiteCauchyTailHandoffFields : FiniteCauchyTailHandoffUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | FiniteCauchyTailHandoffUp.mk regSeqRat streamName dyadicRatCore cauchyModulus
      tailSelector realSeal transport continuation provenance localNameCert =>
      [regSeqRat, streamName, dyadicRatCore, cauchyModulus, tailSelector, realSeal,
        transport, continuation, provenance, localNameCert]

def finiteCauchyTailHandoffToEventFlow : FiniteCauchyTailHandoffUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => List.map finiteCauchyTailHandoffEncodeBHist (finiteCauchyTailHandoffFields x)

private def finiteCauchyTailHandoffEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => finiteCauchyTailHandoffEventAt index rest

def finiteCauchyTailHandoffFromEventFlow
    (ef : EventFlow) : Option FiniteCauchyTailHandoffUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (FiniteCauchyTailHandoffUp.mk
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt Nat.zero ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt (Nat.succ Nat.zero) ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt (Nat.succ (Nat.succ Nat.zero)) ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt (Nat.succ (Nat.succ (Nat.succ Nat.zero))) ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt
          (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt
          (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))) ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt
          (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))) ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt
          (Nat.succ
            (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))
          ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt
          (Nat.succ
            (Nat.succ
              (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero))))))))
          ef))
      (finiteCauchyTailHandoffDecodeBHist
        (finiteCauchyTailHandoffEventAt
          (Nat.succ
            (Nat.succ
              (Nat.succ
                (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))))))
          ef)))

private theorem finiteCauchyTailHandoff_round_trip :
    ∀ x : FiniteCauchyTailHandoffUp,
      finiteCauchyTailHandoffFromEventFlow
        (finiteCauchyTailHandoffToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk regSeqRat streamName dyadicRatCore cauchyModulus tailSelector realSeal transport
      continuation provenance localNameCert =>
      change
        some
          (FiniteCauchyTailHandoffUp.mk
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist regSeqRat))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist streamName))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist dyadicRatCore))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist cauchyModulus))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist tailSelector))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist realSeal))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist transport))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist continuation))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist provenance))
            (finiteCauchyTailHandoffDecodeBHist
              (finiteCauchyTailHandoffEncodeBHist localNameCert))) =
          some
            (FiniteCauchyTailHandoffUp.mk regSeqRat streamName dyadicRatCore cauchyModulus
              tailSelector realSeal transport continuation provenance localNameCert)
      rw [finiteCauchyTailHandoff_decode_encode_bhist regSeqRat,
        finiteCauchyTailHandoff_decode_encode_bhist streamName,
        finiteCauchyTailHandoff_decode_encode_bhist dyadicRatCore,
        finiteCauchyTailHandoff_decode_encode_bhist cauchyModulus,
        finiteCauchyTailHandoff_decode_encode_bhist tailSelector,
        finiteCauchyTailHandoff_decode_encode_bhist realSeal,
        finiteCauchyTailHandoff_decode_encode_bhist transport,
        finiteCauchyTailHandoff_decode_encode_bhist continuation,
        finiteCauchyTailHandoff_decode_encode_bhist provenance,
        finiteCauchyTailHandoff_decode_encode_bhist localNameCert]

private theorem finiteCauchyTailHandoffToEventFlow_injective
    {x y : FiniteCauchyTailHandoffUp} :
    finiteCauchyTailHandoffToEventFlow x =
      finiteCauchyTailHandoffToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      finiteCauchyTailHandoffFromEventFlow (finiteCauchyTailHandoffToEventFlow x) =
        finiteCauchyTailHandoffFromEventFlow (finiteCauchyTailHandoffToEventFlow y) :=
    congrArg finiteCauchyTailHandoffFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (finiteCauchyTailHandoff_round_trip x).symm
      (Eq.trans hread (finiteCauchyTailHandoff_round_trip y)))

instance finiteCauchyTailHandoffBHistCarrier : BHistCarrier FiniteCauchyTailHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := finiteCauchyTailHandoffToEventFlow
  fromEventFlow := finiteCauchyTailHandoffFromEventFlow

instance finiteCauchyTailHandoffChapterTasteGate :
    ChapterTasteGate FiniteCauchyTailHandoffUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      finiteCauchyTailHandoffFromEventFlow
        (finiteCauchyTailHandoffToEventFlow x) = some x
    exact finiteCauchyTailHandoff_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (finiteCauchyTailHandoffToEventFlow_injective heq)

theorem FiniteCauchyTailHandoffNameCertObligations :
    (∀ h : BHist,
      finiteCauchyTailHandoffDecodeBHist (finiteCauchyTailHandoffEncodeBHist h) = h) ∧
      (∀ regSeqRat streamName dyadicRatCore cauchyModulus tailSelector realSeal transport
          continuation provenance localNameCert : BHist,
        FiniteCauchyTailHandoffUp.mk regSeqRat streamName dyadicRatCore cauchyModulus
            tailSelector realSeal transport continuation provenance localNameCert =
          FiniteCauchyTailHandoffUp.mk regSeqRat streamName dyadicRatCore cauchyModulus
            tailSelector realSeal transport continuation provenance localNameCert) ∧
        (∀ regSeqRat₁ streamName₁ dyadicRatCore₁ cauchyModulus₁ tailSelector₁ realSeal₁
            transport₁ continuation₁ provenance₁ localNameCert₁ regSeqRat₂ streamName₂
            dyadicRatCore₂ cauchyModulus₂ tailSelector₂ realSeal₂ transport₂ continuation₂
            provenance₂ localNameCert₂ : BHist,
          FiniteCauchyTailHandoffUp.mk regSeqRat₁ streamName₁ dyadicRatCore₁
              cauchyModulus₁ tailSelector₁ realSeal₁ transport₁ continuation₁ provenance₁
              localNameCert₁ =
            FiniteCauchyTailHandoffUp.mk regSeqRat₂ streamName₂ dyadicRatCore₂
              cauchyModulus₂ tailSelector₂ realSeal₂ transport₂ continuation₂ provenance₂
              localNameCert₂ →
            regSeqRat₁ = regSeqRat₂ ∧ streamName₁ = streamName₂ ∧
              dyadicRatCore₁ = dyadicRatCore₂ ∧ cauchyModulus₁ = cauchyModulus₂ ∧
                tailSelector₁ = tailSelector₂ ∧ realSeal₁ = realSeal₂ ∧
                  transport₁ = transport₂ ∧ continuation₁ = continuation₂ ∧
                    provenance₁ = provenance₂ ∧ localNameCert₁ = localNameCert₂) ∧
          FiniteCauchyTailHandoffUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty ≠
            FiniteCauchyTailHandoffUp.mk (BHist.e1 BHist.Empty) BHist.Empty BHist.Empty
              BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
              BHist.Empty := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · intro h
    induction h with
    | Empty =>
        rfl
    | e0 h ih =>
        exact congrArg BHist.e0 ih
    | e1 h ih =>
        exact congrArg BHist.e1 ih
  · constructor
    · intro regSeqRat streamName dyadicRatCore cauchyModulus tailSelector realSeal transport
        continuation provenance localNameCert
      rfl
    · constructor
      · intro regSeqRat₁ streamName₁ dyadicRatCore₁ cauchyModulus₁ tailSelector₁ realSeal₁
          transport₁ continuation₁ provenance₁ localNameCert₁ regSeqRat₂ streamName₂
          dyadicRatCore₂ cauchyModulus₂ tailSelector₂ realSeal₂ transport₂ continuation₂
          provenance₂ localNameCert₂ h
        cases h
        exact
          ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · intro h
        cases h

end BEDC.Derived
