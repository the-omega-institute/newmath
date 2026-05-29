import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.OrthogonalPolynomialUp

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive OrthogonalPolynomialUp : Type where
  | mk (F M R N Z E H C P A : BHist) : OrthogonalPolynomialUp
  deriving DecidableEq

def orthogonalPolynomialEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: orthogonalPolynomialEncodeBHist h
  | BHist.e1 h => BMark.b1 :: orthogonalPolynomialEncodeBHist h

def orthogonalPolynomialDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (orthogonalPolynomialDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (orthogonalPolynomialDecodeBHist tail)

private theorem orthogonalPolynomialDecodeEncode :
    ∀ h : BHist, orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def orthogonalPolynomialFields : OrthogonalPolynomialUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | OrthogonalPolynomialUp.mk F M R N Z E H C P A => [F, M, R, N, Z, E, H, C, P, A]

def orthogonalPolynomialToEventFlow : OrthogonalPolynomialUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | token => (orthogonalPolynomialFields token).map orthogonalPolynomialEncodeBHist

def orthogonalPolynomialFromEventFlow : EventFlow → Option OrthogonalPolynomialUp
  -- BEDC touchpoint anchor: BHist BMark
  | F :: M :: R :: N :: Z :: E :: H :: C :: P :: A :: [] =>
      some
        (OrthogonalPolynomialUp.mk
          (orthogonalPolynomialDecodeBHist F)
          (orthogonalPolynomialDecodeBHist M)
          (orthogonalPolynomialDecodeBHist R)
          (orthogonalPolynomialDecodeBHist N)
          (orthogonalPolynomialDecodeBHist Z)
          (orthogonalPolynomialDecodeBHist E)
          (orthogonalPolynomialDecodeBHist H)
          (orthogonalPolynomialDecodeBHist C)
          (orthogonalPolynomialDecodeBHist P)
          (orthogonalPolynomialDecodeBHist A))
  | _ => none

private theorem orthogonalPolynomial_round_trip :
    ∀ x : OrthogonalPolynomialUp,
      orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk F M R N Z E H C P A =>
      change
        some
          (OrthogonalPolynomialUp.mk
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist F))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist M))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist R))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist N))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist Z))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist E))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist H))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist C))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist P))
            (orthogonalPolynomialDecodeBHist (orthogonalPolynomialEncodeBHist A))) =
          some (OrthogonalPolynomialUp.mk F M R N Z E H C P A)
      rw [orthogonalPolynomialDecodeEncode F, orthogonalPolynomialDecodeEncode M,
        orthogonalPolynomialDecodeEncode R, orthogonalPolynomialDecodeEncode N,
        orthogonalPolynomialDecodeEncode Z, orthogonalPolynomialDecodeEncode E,
        orthogonalPolynomialDecodeEncode H, orthogonalPolynomialDecodeEncode C,
        orthogonalPolynomialDecodeEncode P, orthogonalPolynomialDecodeEncode A]

private theorem orthogonalPolynomialToEventFlow_injective {x y : OrthogonalPolynomialUp} :
    orthogonalPolynomialToEventFlow x = orthogonalPolynomialToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow x) =
        orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow y) :=
    congrArg orthogonalPolynomialFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (orthogonalPolynomial_round_trip x).symm
      (Eq.trans hread (orthogonalPolynomial_round_trip y)))

instance orthogonalPolynomialBHistCarrier : BHistCarrier OrthogonalPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := orthogonalPolynomialToEventFlow
  fromEventFlow := orthogonalPolynomialFromEventFlow

instance orthogonalPolynomialChapterTasteGate :
    ChapterTasteGate OrthogonalPolynomialUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change orthogonalPolynomialFromEventFlow (orthogonalPolynomialToEventFlow x) = some x
    exact orthogonalPolynomial_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (orthogonalPolynomialToEventFlow_injective heq)

end BEDC.Derived.OrthogonalPolynomialUp
