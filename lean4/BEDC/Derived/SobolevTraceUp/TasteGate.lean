import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.SobolevTraceUp

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

inductive SobolevTraceUp : Type where
  | mk (S D B R M E H C P N : BHist) : SobolevTraceUp
  deriving DecidableEq

private def sobolevTraceEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: sobolevTraceEncodeBHist h
  | BHist.e1 h => BMark.b1 :: sobolevTraceEncodeBHist h

private def sobolevTraceDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (sobolevTraceDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (sobolevTraceDecodeBHist tail)

private theorem sobolevTrace_decode_encode_bhist :
    ∀ h : BHist, sobolevTraceDecodeBHist (sobolevTraceEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

private def sobolevTraceFields : SobolevTraceUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | SobolevTraceUp.mk S D B R M E H C P N => [S, D, B, R, M, E, H, C, P, N]

private def sobolevTraceToEventFlow : SobolevTraceUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (sobolevTraceFields x).map sobolevTraceEncodeBHist

private def sobolevTraceFromEventFlow : EventFlow → Option SobolevTraceUp
  -- BEDC touchpoint anchor: BHist BMark
  | [S, D, B, R, M, E, H, C, P, N] =>
      some
        (SobolevTraceUp.mk
          (sobolevTraceDecodeBHist S)
          (sobolevTraceDecodeBHist D)
          (sobolevTraceDecodeBHist B)
          (sobolevTraceDecodeBHist R)
          (sobolevTraceDecodeBHist M)
          (sobolevTraceDecodeBHist E)
          (sobolevTraceDecodeBHist H)
          (sobolevTraceDecodeBHist C)
          (sobolevTraceDecodeBHist P)
          (sobolevTraceDecodeBHist N))
  | _ => none

private theorem sobolevTrace_round_trip :
    ∀ x : SobolevTraceUp, sobolevTraceFromEventFlow (sobolevTraceToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk S D B R M E H C P N =>
      change
        some
          (SobolevTraceUp.mk
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist S))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist D))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist B))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist R))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist M))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist E))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist H))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist C))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist P))
            (sobolevTraceDecodeBHist (sobolevTraceEncodeBHist N))) =
          some (SobolevTraceUp.mk S D B R M E H C P N)
      rw [sobolevTrace_decode_encode_bhist S, sobolevTrace_decode_encode_bhist D,
        sobolevTrace_decode_encode_bhist B, sobolevTrace_decode_encode_bhist R,
        sobolevTrace_decode_encode_bhist M, sobolevTrace_decode_encode_bhist E,
        sobolevTrace_decode_encode_bhist H, sobolevTrace_decode_encode_bhist C,
        sobolevTrace_decode_encode_bhist P, sobolevTrace_decode_encode_bhist N]

private theorem sobolevTraceToEventFlow_injective {x y : SobolevTraceUp} :
    sobolevTraceToEventFlow x = sobolevTraceToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      sobolevTraceFromEventFlow (sobolevTraceToEventFlow x) =
        sobolevTraceFromEventFlow (sobolevTraceToEventFlow y) :=
    congrArg sobolevTraceFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (sobolevTrace_round_trip x).symm
      (Eq.trans hread (sobolevTrace_round_trip y)))

instance sobolevTraceBHistCarrier : BHistCarrier SobolevTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := sobolevTraceToEventFlow
  fromEventFlow := sobolevTraceFromEventFlow

instance sobolevTraceChapterTasteGate : ChapterTasteGate SobolevTraceUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change sobolevTraceFromEventFlow (sobolevTraceToEventFlow x) = some x
    exact sobolevTrace_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (sobolevTraceToEventFlow_injective heq)

def SobolevTraceCarrier [AskSetup] [PackageSetup]
    (S D B R M E H C P N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory B ∧ UnaryHistory R ∧
    UnaryHistory M ∧ UnaryHistory E ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem SobolevTraceNamecertObligationSurface [AskSetup] [PackageSetup]
    {S D B R M E H C P N boundaryRead compactRead metricRead scalarRead replayRead : BHist}
    {trace : SobolevTraceUp} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SobolevTraceCarrier S D B R M E H C P N bundle pkg →
      SobolevTraceUp.mk S D B R M E H C P N = trace →
        Cont S D boundaryRead →
          Cont boundaryRead B compactRead →
            Cont compactRead M metricRead →
              Cont metricRead E scalarRead →
                Cont H C replayRead →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                            (fun row : BHist => hsame row scalarRead ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row S ∨ hsame row D ∨ hsame row B ∨ hsame row R ∨
                                hsame row M ∨ hsame row E ∨ hsame row scalarRead)
                            (fun row : BHist =>
                              UnaryHistory row ∧ PkgSig bundle P pkg ∧
                                PkgSig bundle N pkg)
                            hsame ∧
                        UnaryHistory boundaryRead ∧ UnaryHistory compactRead ∧
                          UnaryHistory metricRead ∧ UnaryHistory scalarRead ∧
                            UnaryHistory replayRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier _trace boundaryRoute compactRoute metricRoute scalarRoute replayRoute pPkg nPkg
  obtain ⟨sUnary, dUnary, bUnary, _rUnary, mUnary, eUnary, hUnary, cUnary,
    _pUnary, _nUnary, _carrierPPkg, _carrierNPkg⟩ := carrier
  have boundaryUnary : UnaryHistory boundaryRead :=
    unary_cont_closed sUnary dUnary boundaryRoute
  have compactUnary : UnaryHistory compactRead :=
    unary_cont_closed boundaryUnary bUnary compactRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed compactUnary mUnary metricRoute
  have scalarUnary : UnaryHistory scalarRead :=
    unary_cont_closed metricUnary eUnary scalarRoute
  have replayUnary : UnaryHistory replayRead :=
    unary_cont_closed hUnary cUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scalarRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row D ∨ hsame row B ∨ hsame row R ∨
              hsame row M ∨ hsame row E ∨ hsame row scalarRead)
          (fun row : BHist => UnaryHistory row ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro scalarRead ⟨hsame_refl scalarRead, scalarUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, pPkg, nPkg⟩
  }
  exact ⟨cert, boundaryUnary, compactUnary, metricUnary, scalarUnary, replayUnary⟩

end BEDC.Derived.SobolevTraceUp
