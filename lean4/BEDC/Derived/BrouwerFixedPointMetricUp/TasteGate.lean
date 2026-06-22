import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.GroundCompiler.EventFlow
import BEDC.Meta.TasteGate

namespace BEDC.Derived.BrouwerFixedPointMetricUp

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

inductive BrouwerFixedPointMetricUp : Type where
  | mk (K X M G E R H C P N : BHist) : BrouwerFixedPointMetricUp
  deriving DecidableEq

inductive BrouwerFixedPointMetricCarrier
    (K X M G E R H C P N : BHist) : Prop where
  | mk :
      UnaryHistory K →
        UnaryHistory X →
          UnaryHistory M →
            UnaryHistory G →
              UnaryHistory E →
                UnaryHistory R →
                  UnaryHistory H →
                    UnaryHistory C →
                      UnaryHistory P →
                        UnaryHistory N →
                          BrouwerFixedPointMetricCarrier K X M G E R H C P N

def brouwerFixedPointMetricEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: brouwerFixedPointMetricEncodeBHist h
  | BHist.e1 h => BMark.b1 :: brouwerFixedPointMetricEncodeBHist h

def brouwerFixedPointMetricDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (brouwerFixedPointMetricDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (brouwerFixedPointMetricDecodeBHist tail)

private theorem brouwerFixedPointMetric_decode_encode_bhist :
    ∀ h : BHist,
      brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

def brouwerFixedPointMetricFields : BrouwerFixedPointMetricUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | BrouwerFixedPointMetricUp.mk K X M G E R H C P N => [K, X, M, G, E, R, H, C, P, N]

def brouwerFixedPointMetricToEventFlow : BrouwerFixedPointMetricUp → EventFlow :=
  -- BEDC touchpoint anchor: BHist BMark
  fun x => (brouwerFixedPointMetricFields x).map brouwerFixedPointMetricEncodeBHist

private def brouwerFixedPointMetricEventAtDefault : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => brouwerFixedPointMetricEventAtDefault index rest

def brouwerFixedPointMetricFromEventFlow (ef : EventFlow) : Option BrouwerFixedPointMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (BrouwerFixedPointMetricUp.mk
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 0 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 1 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 2 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 3 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 4 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 5 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 6 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 7 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 8 ef))
      (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEventAtDefault 9 ef)))

private theorem brouwerFixedPointMetric_round_trip :
    ∀ x : BrouwerFixedPointMetricUp,
      brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk K X M G E R H C P N =>
      change
        some
          (BrouwerFixedPointMetricUp.mk
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist K))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist X))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist M))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist G))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist E))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist R))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist H))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist C))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist P))
            (brouwerFixedPointMetricDecodeBHist (brouwerFixedPointMetricEncodeBHist N))) =
          some (BrouwerFixedPointMetricUp.mk K X M G E R H C P N)
      rw [brouwerFixedPointMetric_decode_encode_bhist K,
        brouwerFixedPointMetric_decode_encode_bhist X,
        brouwerFixedPointMetric_decode_encode_bhist M,
        brouwerFixedPointMetric_decode_encode_bhist G,
        brouwerFixedPointMetric_decode_encode_bhist E,
        brouwerFixedPointMetric_decode_encode_bhist R,
        brouwerFixedPointMetric_decode_encode_bhist H,
        brouwerFixedPointMetric_decode_encode_bhist C,
        brouwerFixedPointMetric_decode_encode_bhist P,
        brouwerFixedPointMetric_decode_encode_bhist N]

private theorem brouwerFixedPointMetricToEventFlow_injective {x y : BrouwerFixedPointMetricUp} :
    brouwerFixedPointMetricToEventFlow x = brouwerFixedPointMetricToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow x) =
        brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow y) :=
    congrArg brouwerFixedPointMetricFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (brouwerFixedPointMetric_round_trip x).symm
      (Eq.trans hread (brouwerFixedPointMetric_round_trip y)))

private theorem brouwerFixedPointMetric_field_faithful :
    ∀ x y : BrouwerFixedPointMetricUp,
      brouwerFixedPointMetricFields x = brouwerFixedPointMetricFields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk K X M G E R H C P N =>
      cases y with
      | mk K' X' M' G' E' R' H' C' P' N' =>
          cases hfields
          rfl

instance brouwerFixedPointMetricBHistCarrier : BHistCarrier BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := brouwerFixedPointMetricToEventFlow
  fromEventFlow := brouwerFixedPointMetricFromEventFlow

instance brouwerFixedPointMetricChapterTasteGate :
    ChapterTasteGate BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      brouwerFixedPointMetricFromEventFlow (brouwerFixedPointMetricToEventFlow x) = some x
    exact brouwerFixedPointMetric_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (brouwerFixedPointMetricToEventFlow_injective heq)

instance brouwerFixedPointMetricFieldFaithful : FieldFaithful BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := brouwerFixedPointMetricFields
  field_faithful := brouwerFixedPointMetric_field_faithful

instance brouwerFixedPointMetricNontrivial : Nontrivial BrouwerFixedPointMetricUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨BrouwerFixedPointMetricUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      BrouwerFixedPointMetricUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate BrouwerFixedPointMetricUp :=
  -- BEDC touchpoint anchor: BHist BMark
  brouwerFixedPointMetricChapterTasteGate

theorem BrouwerFixedPointMetricCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {K X M G E R H C P N witness residual : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BrouwerFixedPointMetricCarrier K X M G E R H C P N →
      Cont K X M →
        Cont M G witness →
          Cont witness E residual →
            PkgSig bundle P pkg →
              SemanticNameCert
                  (fun row : BHist => hsame row residual ∧ UnaryHistory row)
                  (fun row : BHist =>
                    hsame row K ∨ hsame row X ∨ hsame row M ∨ hsame row G ∨
                      hsame row E ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                        hsame row P ∨ hsame row N ∨ hsame row residual)
                  (fun row : BHist =>
                    UnaryHistory row ∧ Cont K X M ∧ Cont M G witness ∧
                      Cont witness E residual ∧ PkgSig bundle P pkg)
                  hsame ∧ UnaryHistory witness ∧ UnaryHistory residual := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont PkgSig hsame SemanticNameCert
  intro carrier compactMesh mapMesh witnessResidual provenancePkg
  cases carrier with
  | mk kUnary _xUnary mUnary gUnary eUnary _rUnary _hUnary _cUnary _pUnary _nUnary =>
      have witnessUnary : UnaryHistory witness :=
        unary_cont_closed mUnary gUnary mapMesh
      have residualUnary : UnaryHistory residual :=
        unary_cont_closed witnessUnary eUnary witnessResidual
      have cert :
          SemanticNameCert
              (fun row : BHist => hsame row residual ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row K ∨ hsame row X ∨ hsame row M ∨ hsame row G ∨
                  hsame row E ∨ hsame row R ∨ hsame row H ∨ hsame row C ∨
                    hsame row P ∨ hsame row N ∨ hsame row residual)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont K X M ∧ Cont M G witness ∧
                  Cont witness E residual ∧ PkgSig bundle P pkg)
              hsame := {
        core := {
          carrier_inhabited := Exists.intro residual ⟨hsame_refl residual, residualUnary⟩
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
          right
          right
          right
          right
          right
          right
          right
          right
          right
          right
          exact source.left
        ledger_sound := by
          intro _row source
          exact ⟨source.right, compactMesh, mapMesh, witnessResidual, provenancePkg⟩
      }
      exact ⟨cert, witnessUnary, residualUnary⟩

end BEDC.Derived.BrouwerFixedPointMetricUp
