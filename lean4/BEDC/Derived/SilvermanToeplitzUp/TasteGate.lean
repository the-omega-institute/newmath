import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SilvermanToeplitzUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive SilvermanToeplitzUp : Type where
  | mk
      (matrix rowSum columnLimit regularity route realSeal transport replay provenance
        localCert : BHist) :
      SilvermanToeplitzUp
  deriving DecidableEq

def silvermanToeplitzEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: silvermanToeplitzEncodeBHist h
  | BHist.e1 h => BMark.b1 :: silvermanToeplitzEncodeBHist h

def silvermanToeplitzDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (silvermanToeplitzDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (silvermanToeplitzDecodeBHist tail)

private theorem silvermanToeplitz_decode_encode :
    ∀ h : BHist, silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def silvermanToeplitzFields : SilvermanToeplitzUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SilvermanToeplitzUp.mk matrix rowSum columnLimit regularity route realSeal transport replay
      provenance localCert =>
      [matrix, rowSum, columnLimit, regularity, route, realSeal, transport, replay,
        provenance, localCert]

def silvermanToeplitzToEventFlow : SilvermanToeplitzUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (silvermanToeplitzFields x).map silvermanToeplitzEncodeBHist

def silvermanToeplitzFromEventFlow : EventFlow → Option SilvermanToeplitzUp
  -- BEDC touchpoint anchor: BHist BMark
  | matrix :: rowSum :: columnLimit :: regularity :: route :: realSeal :: transport ::
      replay :: provenance :: localCert :: [] =>
      some
        (SilvermanToeplitzUp.mk
          (silvermanToeplitzDecodeBHist matrix)
          (silvermanToeplitzDecodeBHist rowSum)
          (silvermanToeplitzDecodeBHist columnLimit)
          (silvermanToeplitzDecodeBHist regularity)
          (silvermanToeplitzDecodeBHist route)
          (silvermanToeplitzDecodeBHist realSeal)
          (silvermanToeplitzDecodeBHist transport)
          (silvermanToeplitzDecodeBHist replay)
          (silvermanToeplitzDecodeBHist provenance)
          (silvermanToeplitzDecodeBHist localCert))
  | _ => none

private theorem silvermanToeplitz_round_trip :
    ∀ x : SilvermanToeplitzUp,
      silvermanToeplitzFromEventFlow (silvermanToeplitzToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk matrix rowSum columnLimit regularity route realSeal transport replay provenance
      localCert =>
      change
        some
          (SilvermanToeplitzUp.mk
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist matrix))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist rowSum))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist columnLimit))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist regularity))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist route))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist realSeal))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist transport))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist replay))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist provenance))
            (silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist localCert))) =
          some
            (SilvermanToeplitzUp.mk matrix rowSum columnLimit regularity route realSeal
              transport replay provenance localCert)
      rw [silvermanToeplitz_decode_encode matrix, silvermanToeplitz_decode_encode rowSum,
        silvermanToeplitz_decode_encode columnLimit,
        silvermanToeplitz_decode_encode regularity, silvermanToeplitz_decode_encode route,
        silvermanToeplitz_decode_encode realSeal,
        silvermanToeplitz_decode_encode transport, silvermanToeplitz_decode_encode replay,
        silvermanToeplitz_decode_encode provenance,
        silvermanToeplitz_decode_encode localCert]

private theorem silvermanToeplitzToEventFlow_injective {x y : SilvermanToeplitzUp} :
    silvermanToeplitzToEventFlow x = silvermanToeplitzToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      silvermanToeplitzFromEventFlow (silvermanToeplitzToEventFlow x) =
        silvermanToeplitzFromEventFlow (silvermanToeplitzToEventFlow y) :=
    congrArg silvermanToeplitzFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (silvermanToeplitz_round_trip x).symm
      (Eq.trans hread (silvermanToeplitz_round_trip y)))

private theorem silvermanToeplitzEncodeBHist_injective {h k : BHist} :
    silvermanToeplitzEncodeBHist h = silvermanToeplitzEncodeBHist k → h = k := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  calc
    h = silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist h) :=
      (silvermanToeplitz_decode_encode h).symm
    _ = silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist k) :=
      congrArg silvermanToeplitzDecodeBHist heq
    _ = k := silvermanToeplitz_decode_encode k

private theorem silvermanToeplitzToEventFlow_direct_injective
    {x y : SilvermanToeplitzUp} :
    silvermanToeplitzToEventFlow x = silvermanToeplitzToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  cases x with
  | mk matrix₁ rowSum₁ columnLimit₁ regularity₁ route₁ realSeal₁ transport₁ replay₁
      provenance₁ localCert₁ =>
      cases y with
      | mk matrix₂ rowSum₂ columnLimit₂ regularity₂ route₂ realSeal₂ transport₂ replay₂
          provenance₂ localCert₂ =>
          change
            [silvermanToeplitzEncodeBHist matrix₁,
              silvermanToeplitzEncodeBHist rowSum₁,
              silvermanToeplitzEncodeBHist columnLimit₁,
              silvermanToeplitzEncodeBHist regularity₁,
              silvermanToeplitzEncodeBHist route₁,
              silvermanToeplitzEncodeBHist realSeal₁,
              silvermanToeplitzEncodeBHist transport₁,
              silvermanToeplitzEncodeBHist replay₁,
              silvermanToeplitzEncodeBHist provenance₁,
              silvermanToeplitzEncodeBHist localCert₁] =
              [silvermanToeplitzEncodeBHist matrix₂,
                silvermanToeplitzEncodeBHist rowSum₂,
                silvermanToeplitzEncodeBHist columnLimit₂,
                silvermanToeplitzEncodeBHist regularity₂,
                silvermanToeplitzEncodeBHist route₂,
                silvermanToeplitzEncodeBHist realSeal₂,
                silvermanToeplitzEncodeBHist transport₂,
                silvermanToeplitzEncodeBHist replay₂,
                silvermanToeplitzEncodeBHist provenance₂,
                silvermanToeplitzEncodeBHist localCert₂] at heq
          injection heq with hMatrix tail0
          injection tail0 with hRowSum tail1
          injection tail1 with hColumnLimit tail2
          injection tail2 with hRegularity tail3
          injection tail3 with hRoute tail4
          injection tail4 with hRealSeal tail5
          injection tail5 with hTransport tail6
          injection tail6 with hReplay tail7
          injection tail7 with hProvenance tail8
          injection tail8 with hLocalCert _
          have matrixEq := silvermanToeplitzEncodeBHist_injective hMatrix
          have rowSumEq := silvermanToeplitzEncodeBHist_injective hRowSum
          have columnLimitEq := silvermanToeplitzEncodeBHist_injective hColumnLimit
          have regularityEq := silvermanToeplitzEncodeBHist_injective hRegularity
          have routeEq := silvermanToeplitzEncodeBHist_injective hRoute
          have realSealEq := silvermanToeplitzEncodeBHist_injective hRealSeal
          have transportEq := silvermanToeplitzEncodeBHist_injective hTransport
          have replayEq := silvermanToeplitzEncodeBHist_injective hReplay
          have provenanceEq := silvermanToeplitzEncodeBHist_injective hProvenance
          have localCertEq := silvermanToeplitzEncodeBHist_injective hLocalCert
          subst matrixEq
          subst rowSumEq
          subst columnLimitEq
          subst regularityEq
          subst routeEq
          subst realSealEq
          subst transportEq
          subst replayEq
          subst provenanceEq
          subst localCertEq
          rfl

instance silvermanToeplitzBHistCarrier : BHistCarrier SilvermanToeplitzUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := silvermanToeplitzToEventFlow
  fromEventFlow := silvermanToeplitzFromEventFlow

instance silvermanToeplitzChapterTasteGate : ChapterTasteGate SilvermanToeplitzUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change silvermanToeplitzFromEventFlow (silvermanToeplitzToEventFlow x) = some x
    exact silvermanToeplitz_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (silvermanToeplitzToEventFlow_injective heq)

def taste_gate : ChapterTasteGate SilvermanToeplitzUp :=
  -- BEDC touchpoint anchor: BHist BMark
  silvermanToeplitzChapterTasteGate

theorem SilvermanToeplitzTasteGate_single_carrier_alignment :
    (∀ h : BHist, silvermanToeplitzDecodeBHist (silvermanToeplitzEncodeBHist h) = h) ∧
      (∀ x y : SilvermanToeplitzUp,
        silvermanToeplitzToEventFlow x = silvermanToeplitzToEventFlow y → x = y) ∧
        silvermanToeplitzEncodeBHist BHist.Empty = ([] : List BMark) := by
  -- BEDC touchpoint anchor: BHist BMark
  constructor
  · exact silvermanToeplitz_decode_encode
  constructor
  · intro x y heq
    exact silvermanToeplitzToEventFlow_direct_injective heq
  · rfl

end BEDC.Derived.SilvermanToeplitzUp
