import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.EpigraphUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive EpigraphUp : Type where
  | mk (D V L O H C P N : BHist) : EpigraphUp
  deriving DecidableEq

def epigraphEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: epigraphEncodeBHist h
  | BHist.e1 h => BMark.b1 :: epigraphEncodeBHist h

def epigraphDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (epigraphDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (epigraphDecodeBHist tail)

private theorem epigraphDecode_encode_bhist :
    ∀ h : BHist, epigraphDecodeBHist (epigraphEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def epigraphFields : EpigraphUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | EpigraphUp.mk D V L O H C P N => [D, V, L, O, H, C, P, N]

def epigraphToEventFlow : EpigraphUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (epigraphFields x).map epigraphEncodeBHist

def epigraphFromEventFlow : EventFlow → Option EpigraphUp
  -- BEDC touchpoint anchor: BHist BMark
  | D :: V :: L :: O :: H :: C :: P :: N :: [] =>
      some
        (EpigraphUp.mk
          (epigraphDecodeBHist D)
          (epigraphDecodeBHist V)
          (epigraphDecodeBHist L)
          (epigraphDecodeBHist O)
          (epigraphDecodeBHist H)
          (epigraphDecodeBHist C)
          (epigraphDecodeBHist P)
          (epigraphDecodeBHist N))
  | _ => none

private theorem epigraph_round_trip :
    ∀ x : EpigraphUp, epigraphFromEventFlow (epigraphToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D V L O H C P N =>
      simp only [epigraphToEventFlow, epigraphFields, epigraphFromEventFlow, List.map_cons,
        List.map_nil, epigraphDecode_encode_bhist]

private theorem epigraphToEventFlow_injective {x y : EpigraphUp} :
    epigraphToEventFlow x = epigraphToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      epigraphFromEventFlow (epigraphToEventFlow x) =
        epigraphFromEventFlow (epigraphToEventFlow y) :=
    congrArg epigraphFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (epigraph_round_trip x).symm (Eq.trans hread (epigraph_round_trip y)))

instance epigraphBHistCarrier : BHistCarrier EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := epigraphToEventFlow
  fromEventFlow := epigraphFromEventFlow

instance epigraphChapterTasteGate : ChapterTasteGate EpigraphUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change epigraphFromEventFlow (epigraphToEventFlow x) = some x
    exact epigraph_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (epigraphToEventFlow_injective heq)

end BEDC.Derived.EpigraphUp
