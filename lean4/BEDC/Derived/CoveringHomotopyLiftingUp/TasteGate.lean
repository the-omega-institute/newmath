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

namespace BEDC.Derived.CoveringHomotopyLiftingUp

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

inductive CoveringHomotopyLiftingUp : Type where
  -- BEDC touchpoint anchor: BHist BMark
  | mk (F pi f0 I U W Sigma E H C P N : BHist) : CoveringHomotopyLiftingUp
  deriving DecidableEq

def CoveringHomotopyLiftingCarrier [AskSetup] [PackageSetup]
    (F pi f0 I U W Sigma E H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory PkgSig
  UnaryHistory F ∧ UnaryHistory pi ∧ UnaryHistory f0 ∧ UnaryHistory I ∧
    UnaryHistory U ∧ UnaryHistory W ∧ UnaryHistory Sigma ∧ UnaryHistory E ∧
      UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory N ∧
        PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem CoveringHomotopyLiftingNameCert_obligations [AskSetup] [PackageSetup]
    {F pi f0 I U W Sigma E H C P N liftRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CoveringHomotopyLiftingCarrier F pi f0 I U W Sigma E H C P N bundle pkg →
      Cont C N liftRead →
        PkgSig bundle liftRead pkg →
          SemanticNameCert
              (fun row : BHist => hsame row liftRead ∧ UnaryHistory row)
              (fun row : BHist =>
                hsame row F ∨ hsame row pi ∨ hsame row f0 ∨ hsame row I ∨
                  hsame row U ∨ hsame row W ∨ hsame row Sigma ∨ hsame row E ∨
                    hsame row liftRead)
              (fun row : BHist =>
                UnaryHistory row ∧ Cont C N liftRead ∧ PkgSig bundle liftRead pkg)
              hsame ∧
            UnaryHistory liftRead := by
  -- BEDC touchpoint anchor: CoveringHomotopyLiftingCarrier BHist Cont PkgSig hsame SemanticNameCert
  intro carrier replayRoute liftPkg
  obtain ⟨_fUnary, _piUnary, _f0Unary, _iUnary, _uUnary, _wUnary, _sigmaUnary,
    _eUnary, _hUnary, cUnary, _pUnary, nUnary, _provenancePkg, _namePkg⟩ := carrier
  have liftUnary : UnaryHistory liftRead :=
    unary_cont_closed cUnary nUnary replayRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row liftRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row F ∨ hsame row pi ∨ hsame row f0 ∨ hsame row I ∨
              hsame row U ∨ hsame row W ∨ hsame row Sigma ∨ hsame row E ∨
                hsame row liftRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont C N liftRead ∧ PkgSig bundle liftRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro liftRead ⟨hsame_refl liftRead, liftUnary⟩
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
      exact Or.inr
        (Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, replayRoute, liftPkg⟩
  }
  exact ⟨cert, liftUnary⟩

def CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist :
    BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 ::
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist h
  | BHist.e1 h => BMark.b1 ::
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist h

def CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist :
    RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail =>
      BHist.e0 (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist tail)
  | BMark.b1 :: tail =>
      BHist.e1 (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist tail)

private theorem CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode :
    ∀ h : BHist,
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fields :
    CoveringHomotopyLiftingUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CoveringHomotopyLiftingUp.mk F pi f0 I U W Sigma E H C P N =>
      [F, pi, f0, I, U, W, Sigma, E, H, C, P, N]

def CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow :
    CoveringHomotopyLiftingUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x =>
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fields x).map
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist

private def CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt :
    Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest =>
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt index rest

def CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fromEventFlow
    (ef : EventFlow) : Option CoveringHomotopyLiftingUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CoveringHomotopyLiftingUp.mk
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 0 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 1 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 2 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 3 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 4 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 5 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 6 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 7 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 8 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 9 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 10 ef))
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_eventAt 11 ef)))

private theorem CoveringHomotopyLiftingTasteGate_single_carrier_alignment_round_trip
    (x : CoveringHomotopyLiftingUp) :
    CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fromEventFlow
      (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk F pi f0 I U W Sigma E H C P N =>
      change
        some
          (CoveringHomotopyLiftingUp.mk
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist F))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist pi))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist f0))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist I))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist U))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist W))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist Sigma))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist E))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist H))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist C))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist P))
            (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decodeBHist
              (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_encodeBHist N))) =
          some (CoveringHomotopyLiftingUp.mk F pi f0 I U W Sigma E H C P N)
      rw [CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode F,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode pi,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode f0,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode I,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode U,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode W,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode Sigma,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode E,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode H,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode C,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode P,
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_decode_encode N]

private theorem CoveringHomotopyLiftingTasteGate_single_carrier_alignment_injective
    {x y : CoveringHomotopyLiftingUp} :
    CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow x =
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fromEventFlow
          (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow x) =
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fromEventFlow
          (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow y) :=
    congrArg CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_round_trip x).symm
      (Eq.trans hread
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_round_trip y)))

private theorem CoveringHomotopyLiftingTasteGate_single_carrier_alignment_field_faithful :
    ∀ x y : CoveringHomotopyLiftingUp,
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fields x =
        CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fields y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk F1 pi1 f01 I1 U1 W1 Sigma1 E1 H1 C1 P1 N1 =>
      cases y with
      | mk F2 pi2 f02 I2 U2 W2 Sigma2 E2 H2 C2 P2 N2 =>
          cases hfields
          rfl

instance coveringHomotopyLiftingBHistCarrier : BHistCarrier CoveringHomotopyLiftingUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow
  fromEventFlow := CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fromEventFlow

instance coveringHomotopyLiftingChapterTasteGate :
    ChapterTasteGate CoveringHomotopyLiftingUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change
      CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fromEventFlow
        (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_toEventFlow x) = some x
    exact CoveringHomotopyLiftingTasteGate_single_carrier_alignment_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (CoveringHomotopyLiftingTasteGate_single_carrier_alignment_injective heq)

instance coveringHomotopyLiftingFieldFaithful :
    FieldFaithful CoveringHomotopyLiftingUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := CoveringHomotopyLiftingTasteGate_single_carrier_alignment_fields
  field_faithful := CoveringHomotopyLiftingTasteGate_single_carrier_alignment_field_faithful

theorem CoveringHomotopyLiftingTasteGate_single_carrier_alignment :
    Nonempty (ChapterTasteGate CoveringHomotopyLiftingUp) ∧
      Nonempty (FieldFaithful CoveringHomotopyLiftingUp) := by
  -- BEDC touchpoint anchor: BHist BMark ChapterTasteGate FieldFaithful
  exact ⟨⟨coveringHomotopyLiftingChapterTasteGate⟩, ⟨coveringHomotopyLiftingFieldFaithful⟩⟩

end BEDC.Derived.CoveringHomotopyLiftingUp
