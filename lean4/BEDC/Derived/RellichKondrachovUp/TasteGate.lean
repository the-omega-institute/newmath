import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RellichKondrachovUp [AskSetup] [PackageSetup]
    (domain weakDerivative sobolev embedding compactMetric completeMetric schedule ledger
      transport provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  UnaryHistory domain ∧ UnaryHistory weakDerivative ∧ UnaryHistory sobolev ∧
    UnaryHistory embedding ∧ UnaryHistory compactMetric ∧ UnaryHistory completeMetric ∧
      UnaryHistory schedule ∧ UnaryHistory ledger ∧ UnaryHistory transport ∧
        UnaryHistory provenance ∧ UnaryHistory localName ∧
          Cont weakDerivative sobolev embedding ∧ Cont compactMetric completeMetric schedule ∧
            Cont schedule ledger provenance ∧ hsame transport ledger ∧
              PkgSig bundle provenance pkg ∧ PkgSig bundle localName pkg

end BEDC.Derived

namespace BEDC.Derived.RellichKondrachovUp

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

inductive RellichKondrachovUp : Type where
  | mk (D W S E C M T L H P N : BHist) : RellichKondrachovUp
  deriving DecidableEq

def rellichKondrachovEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: rellichKondrachovEncodeBHist h
  | BHist.e1 h => BMark.b1 :: rellichKondrachovEncodeBHist h

def rellichKondrachovDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (rellichKondrachovDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (rellichKondrachovDecodeBHist tail)

private theorem rellichKondrachov_decode_encode_bhist :
    ∀ h : BHist, rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def rellichKondrachovFields : RellichKondrachovUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | RellichKondrachovUp.mk D W S E C M T L H P N => [D, W, S, E, C, M, T, L, H, P, N]

def rellichKondrachovToEventFlow : RellichKondrachovUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (rellichKondrachovFields x).map rellichKondrachovEncodeBHist

def rellichKondrachovFromEventFlow : EventFlow → Option RellichKondrachovUp
  -- BEDC touchpoint anchor: BHist BMark
  | [] => none
  | _D :: [] => none
  | _D :: _W :: [] => none
  | _D :: _W :: _S :: [] => none
  | _D :: _W :: _S :: _E :: [] => none
  | _D :: _W :: _S :: _E :: _C :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: _H :: [] => none
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: _H :: _P :: [] => none
  | D :: W :: S :: E :: C :: M :: T :: L :: H :: P :: N :: [] =>
      some
        (RellichKondrachovUp.mk
          (rellichKondrachovDecodeBHist D)
          (rellichKondrachovDecodeBHist W)
          (rellichKondrachovDecodeBHist S)
          (rellichKondrachovDecodeBHist E)
          (rellichKondrachovDecodeBHist C)
          (rellichKondrachovDecodeBHist M)
          (rellichKondrachovDecodeBHist T)
          (rellichKondrachovDecodeBHist L)
          (rellichKondrachovDecodeBHist H)
          (rellichKondrachovDecodeBHist P)
          (rellichKondrachovDecodeBHist N))
  | _D :: _W :: _S :: _E :: _C :: _M :: _T :: _L :: _H :: _P :: _N ::
      _extra :: _rest =>
      none

private theorem rellichKondrachov_round_trip :
    ∀ x : RellichKondrachovUp,
      rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk D W S E C M T L H P N =>
      change
        some
          (RellichKondrachovUp.mk
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist D))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist W))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist S))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist E))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist C))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist M))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist T))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist L))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist H))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist P))
            (rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist N))) =
          some (RellichKondrachovUp.mk D W S E C M T L H P N)
      rw [rellichKondrachov_decode_encode_bhist D,
        rellichKondrachov_decode_encode_bhist W,
        rellichKondrachov_decode_encode_bhist S,
        rellichKondrachov_decode_encode_bhist E,
        rellichKondrachov_decode_encode_bhist C,
        rellichKondrachov_decode_encode_bhist M,
        rellichKondrachov_decode_encode_bhist T,
        rellichKondrachov_decode_encode_bhist L,
        rellichKondrachov_decode_encode_bhist H,
        rellichKondrachov_decode_encode_bhist P,
        rellichKondrachov_decode_encode_bhist N]

private theorem rellichKondrachovToEventFlow_injective {x y : RellichKondrachovUp} :
    rellichKondrachovToEventFlow x = rellichKondrachovToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) =
        rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow y) :=
    congrArg rellichKondrachovFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (rellichKondrachov_round_trip x).symm
      (Eq.trans hread (rellichKondrachov_round_trip y)))

instance rellichKondrachovBHistCarrier : BHistCarrier RellichKondrachovUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := rellichKondrachovToEventFlow
  fromEventFlow := rellichKondrachovFromEventFlow

instance rellichKondrachovChapterTasteGate : ChapterTasteGate RellichKondrachovUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) = some x
    exact rellichKondrachov_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (rellichKondrachovToEventFlow_injective heq)

def taste_gate : ChapterTasteGate RellichKondrachovUp :=
  -- BEDC touchpoint anchor: BHist BMark
  rellichKondrachovChapterTasteGate

theorem RellichKondrachovTasteGate_single_carrier_alignment :
    Nonempty (BHistCarrier RellichKondrachovUp) ∧
      Nonempty (ChapterTasteGate RellichKondrachovUp) ∧
        (∀ h : BHist, rellichKondrachovDecodeBHist (rellichKondrachovEncodeBHist h) = h) ∧
          (∀ x : RellichKondrachovUp,
            rellichKondrachovFromEventFlow (rellichKondrachovToEventFlow x) = some x) ∧
            rellichKondrachovEncodeBHist BHist.Empty = ([] : RawEvent) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate
  exact
    ⟨Nonempty.intro rellichKondrachovBHistCarrier,
      Nonempty.intro rellichKondrachovChapterTasteGate,
      rellichKondrachov_decode_encode_bhist,
      rellichKondrachov_round_trip,
      rfl⟩

theorem RellichKondrachovCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {domain weakDerivative sobolev embedding compactMetric completeMetric schedule ledger
      transport provenance localName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BEDC.Derived.RellichKondrachovUp domain weakDerivative sobolev embedding compactMetric
      completeMetric schedule ledger transport provenance localName bundle pkg →
      SemanticNameCert
        (fun row : BHist =>
          BEDC.Derived.RellichKondrachovUp domain weakDerivative sobolev embedding
            compactMetric completeMetric schedule ledger transport provenance localName
            bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.RellichKondrachovUp domain weakDerivative sobolev embedding
            compactMetric completeMetric schedule ledger transport provenance localName
            bundle pkg ∧ hsame row localName)
        (fun row : BHist =>
          BEDC.Derived.RellichKondrachovUp domain weakDerivative sobolev embedding
            compactMetric completeMetric schedule ledger transport provenance localName
            bundle pkg ∧ hsame row localName)
        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro carrier
  have carrierWitness :
      BEDC.Derived.RellichKondrachovUp domain weakDerivative sobolev embedding compactMetric
        completeMetric schedule ledger transport provenance localName bundle pkg :=
    carrier
  exact {
    core := {
      carrier_inhabited := Exists.intro localName ⟨carrierWitness, hsame_refl localName⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _other same
        exact hsame_symm same
      equiv_trans := by
        intro _row _middle _other sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _other same source
        exact ⟨source.left, hsame_trans (hsame_symm same) source.right⟩
    }
    pattern_sound := by
      intro _row source
      exact source
    ledger_sound := by
      intro _row source
      exact source
  }

end BEDC.Derived.RellichKondrachovUp
