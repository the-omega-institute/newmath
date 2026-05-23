import BEDC.FKernel.Hist
import BEDC.FKernel.Mark
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.Meta.TasteGate

namespace BEDC.Derived.ClaimRegistryLayerUp.TasteGate

open BEDC.FKernel.Hist
open BEDC.FKernel.Mark
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.GroundCompiler.EventFlow
open BEDC.Meta.TasteGate

inductive ClaimRegistryLayerUp : Type where
  | mk :
      (entry refusal closureStatus formalTarget provenance verificationReadback transport
        packageProvenance name : BHist) →
      ClaimRegistryLayerUp
  deriving DecidableEq

def claimRegistryLayerEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: claimRegistryLayerEncodeBHist h
  | BHist.e1 h => BMark.b1 :: claimRegistryLayerEncodeBHist h

def claimRegistryLayerDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (claimRegistryLayerDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (claimRegistryLayerDecodeBHist tail)

private def claimRegistryLayerNthRawEvent : EventFlow → Nat → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | [], _ => []
  | head :: _tail, Nat.zero => head
  | _head :: tail, Nat.succ n => claimRegistryLayerNthRawEvent tail n

private theorem claimRegistryLayer_decode_encode_bhist :
    ∀ h : BHist, claimRegistryLayerDecodeBHist (claimRegistryLayerEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty =>
      rfl
  | e0 h ih =>
      exact congrArg BHist.e0 ih
  | e1 h ih =>
      exact congrArg BHist.e1 ih

private theorem claimRegistryLayer_mk_congr
    {entry entry' refusal refusal' closureStatus closureStatus' formalTarget formalTarget'
      provenance provenance' verificationReadback verificationReadback' transport transport'
      packageProvenance packageProvenance' name name' : BHist}
    (hEntry : entry' = entry)
    (hRefusal : refusal' = refusal)
    (hClosureStatus : closureStatus' = closureStatus)
    (hFormalTarget : formalTarget' = formalTarget)
    (hProvenance : provenance' = provenance)
    (hVerificationReadback : verificationReadback' = verificationReadback)
    (hTransport : transport' = transport)
    (hPackageProvenance : packageProvenance' = packageProvenance)
    (hName : name' = name) :
    ClaimRegistryLayerUp.mk entry' refusal' closureStatus' formalTarget' provenance'
        verificationReadback' transport' packageProvenance' name' =
      ClaimRegistryLayerUp.mk entry refusal closureStatus formalTarget provenance
        verificationReadback transport packageProvenance name := by
  -- BEDC touchpoint anchor: BHist BMark
  cases hEntry
  cases hRefusal
  cases hClosureStatus
  cases hFormalTarget
  cases hProvenance
  cases hVerificationReadback
  cases hTransport
  cases hPackageProvenance
  cases hName
  rfl

def claimRegistryLayerFields : ClaimRegistryLayerUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | ClaimRegistryLayerUp.mk entry refusal closureStatus formalTarget provenance
      verificationReadback transport packageProvenance name =>
      [entry, refusal, closureStatus, formalTarget, provenance, verificationReadback, transport,
        packageProvenance, name]

def claimRegistryLayerToEventFlow : ClaimRegistryLayerUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | ClaimRegistryLayerUp.mk entry refusal closureStatus formalTarget provenance
      verificationReadback transport packageProvenance name =>
      [claimRegistryLayerEncodeBHist entry,
        claimRegistryLayerEncodeBHist refusal,
        claimRegistryLayerEncodeBHist closureStatus,
        claimRegistryLayerEncodeBHist formalTarget,
        claimRegistryLayerEncodeBHist provenance,
        claimRegistryLayerEncodeBHist verificationReadback,
        claimRegistryLayerEncodeBHist transport,
        claimRegistryLayerEncodeBHist packageProvenance,
        claimRegistryLayerEncodeBHist name]

def claimRegistryLayerFromEventFlow (ef : EventFlow) : Option ClaimRegistryLayerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (ClaimRegistryLayerUp.mk
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 0))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 1))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 2))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 3))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 4))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 5))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 6))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 7))
      (claimRegistryLayerDecodeBHist (claimRegistryLayerNthRawEvent ef 8)))

private theorem claimRegistryLayer_round_trip :
    ∀ x : ClaimRegistryLayerUp,
      claimRegistryLayerFromEventFlow (claimRegistryLayerToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x
  cases x with
  | mk entry refusal closureStatus formalTarget provenance verificationReadback transport
      packageProvenance name =>
      exact
        congrArg some
          (claimRegistryLayer_mk_congr
            (claimRegistryLayer_decode_encode_bhist entry)
            (claimRegistryLayer_decode_encode_bhist refusal)
            (claimRegistryLayer_decode_encode_bhist closureStatus)
            (claimRegistryLayer_decode_encode_bhist formalTarget)
            (claimRegistryLayer_decode_encode_bhist provenance)
            (claimRegistryLayer_decode_encode_bhist verificationReadback)
            (claimRegistryLayer_decode_encode_bhist transport)
            (claimRegistryLayer_decode_encode_bhist packageProvenance)
            (claimRegistryLayer_decode_encode_bhist name))

private theorem claimRegistryLayerToEventFlow_injective {x y : ClaimRegistryLayerUp} :
    claimRegistryLayerToEventFlow x = claimRegistryLayerToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      claimRegistryLayerFromEventFlow (claimRegistryLayerToEventFlow x) =
        claimRegistryLayerFromEventFlow (claimRegistryLayerToEventFlow y) :=
    congrArg claimRegistryLayerFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (claimRegistryLayer_round_trip x).symm
      (Eq.trans hread (claimRegistryLayer_round_trip y)))

private theorem claimRegistryLayer_field_faithful :
    ∀ x y : ClaimRegistryLayerUp, claimRegistryLayerFields x = claimRegistryLayerFields y →
      x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro x y hfields
  cases x with
  | mk entry refusal closureStatus formalTarget provenance verificationReadback transport
      packageProvenance name =>
      cases y with
      | mk entry' refusal' closureStatus' formalTarget' provenance' verificationReadback'
          transport' packageProvenance' name' =>
          cases hfields
          rfl

instance claimRegistryLayerBHistCarrier : BHistCarrier ClaimRegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := claimRegistryLayerToEventFlow
  fromEventFlow := claimRegistryLayerFromEventFlow

instance claimRegistryLayerChapterTasteGate :
    ChapterTasteGate ClaimRegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := by
    intro x
    change claimRegistryLayerFromEventFlow (claimRegistryLayerToEventFlow x) = some x
    exact claimRegistryLayer_round_trip x
  layer_separation := by
    intro x y hxy heq
    exact hxy (claimRegistryLayerToEventFlow_injective heq)

instance claimRegistryLayerFieldFaithful : FieldFaithful ClaimRegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  fields := claimRegistryLayerFields
  field_faithful := claimRegistryLayer_field_faithful

instance claimRegistryLayerNontrivial : Nontrivial ClaimRegistryLayerUp where
  -- BEDC touchpoint anchor: BHist BMark
  witness_pair :=
    ⟨ClaimRegistryLayerUp.mk BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      ClaimRegistryLayerUp.mk (BHist.e0 BHist.Empty) BHist.Empty BHist.Empty BHist.Empty
        BHist.Empty BHist.Empty BHist.Empty BHist.Empty BHist.Empty,
      by
        intro h
        cases h⟩

def taste_gate : ChapterTasteGate ClaimRegistryLayerUp :=
  -- BEDC touchpoint anchor: BHist BMark
  claimRegistryLayerChapterTasteGate

theorem ClaimRegistryLayerTasteGate_single_carrier_alignment :
    (∀ h : BHist, claimRegistryLayerDecodeBHist (claimRegistryLayerEncodeBHist h) = h) ∧
      (∀ x : ClaimRegistryLayerUp,
        claimRegistryLayerFromEventFlow (claimRegistryLayerToEventFlow x) = some x) ∧
        (∀ x y : ClaimRegistryLayerUp,
          claimRegistryLayerToEventFlow x = claimRegistryLayerToEventFlow y → x = y) ∧
          claimRegistryLayerEncodeBHist BHist.Empty = ([] : List BMark) := by
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
    · intro x
      cases x with
      | mk entry refusal closureStatus formalTarget provenance verificationReadback transport
          packageProvenance name =>
          exact
            congrArg some
              (claimRegistryLayer_mk_congr
                (claimRegistryLayer_decode_encode_bhist entry)
                (claimRegistryLayer_decode_encode_bhist refusal)
                (claimRegistryLayer_decode_encode_bhist closureStatus)
                (claimRegistryLayer_decode_encode_bhist formalTarget)
                (claimRegistryLayer_decode_encode_bhist provenance)
                (claimRegistryLayer_decode_encode_bhist verificationReadback)
                (claimRegistryLayer_decode_encode_bhist transport)
                (claimRegistryLayer_decode_encode_bhist packageProvenance)
                (claimRegistryLayer_decode_encode_bhist name))
    · constructor
      · intro x y heq
        have hread :
            claimRegistryLayerFromEventFlow (claimRegistryLayerToEventFlow x) =
              claimRegistryLayerFromEventFlow (claimRegistryLayerToEventFlow y) :=
          congrArg claimRegistryLayerFromEventFlow heq
        exact Option.some.inj
          (Eq.trans (claimRegistryLayer_round_trip x).symm
            (Eq.trans hread (claimRegistryLayer_round_trip y)))
      · rfl

theorem ClaimRegistryLayer_no_unregistered_export_certificate [AskSetup] [PackageSetup]
    {B C F V H P N attempted : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle attempted pkg →
      hsame attempted N →
        claimRegistryLayerFields
            (ClaimRegistryLayerUp.mk BHist.Empty BHist.Empty B C F V H P N) =
            [BHist.Empty, BHist.Empty, B, C, F, V, H, P, N] ∧
          SemanticNameCert
            (fun row : BHist => hsame row N)
            (fun row : BHist =>
              hsame row BHist.Empty ∨ hsame row B ∨ hsame row C ∨ hsame row F ∨
                hsame row V ∨ hsame row H ∨ hsame row P ∨ hsame row N)
            (fun row : BHist => hsame row attempted ∧ PkgSig bundle attempted pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro pkgAttempted attemptedSameName
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row N)
        (fun row : BHist =>
          hsame row BHist.Empty ∨ hsame row B ∨ hsame row C ∨ hsame row F ∨
            hsame row V ∨ hsame row H ∨ hsame row P ∨ hsame row N)
        (fun row : BHist => hsame row attempted ∧ PkgSig bundle attempted pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro N (hsame_refl N)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source))))))
    ledger_sound := by
      intro _row source
      exact ⟨hsame_trans source (hsame_symm attemptedSameName), pkgAttempted⟩
  }
  exact ⟨rfl, cert⟩

theorem ClaimRegistryLayer_export_control_certificate [AskSetup] [PackageSetup]
    {E R B C F V H P N cited : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PkgSig bundle cited pkg →
      hsame cited E →
        claimRegistryLayerFields (ClaimRegistryLayerUp.mk E R B C F V H P N) =
            [E, R, B, C, F, V, H, P, N] ∧
          SemanticNameCert
            (fun row : BHist => hsame row E)
            (fun row : BHist =>
              hsame row E ∨ hsame row R ∨ hsame row B ∨ hsame row C ∨ hsame row F ∨
                hsame row V ∨ hsame row H ∨ hsame row P ∨ hsame row N)
            (fun row : BHist => hsame row cited ∧ PkgSig bundle cited pkg)
            hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg SemanticNameCert hsame
  intro pkgCited citedSameEntry
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row E)
        (fun row : BHist =>
          hsame row E ∨ hsame row R ∨ hsame row B ∨ hsame row C ∨ hsame row F ∨
            hsame row V ∨ hsame row H ∨ hsame row P ∨ hsame row N)
        (fun row : BHist => hsame row cited ∧ PkgSig bundle cited pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro E (hsame_refl E)
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
        exact hsame_trans (hsame_symm sameRows) source
    }
    pattern_sound := by
      intro _row source
      exact Or.inl source
    ledger_sound := by
      intro _row source
      exact ⟨hsame_trans source (hsame_symm citedSameEntry), pkgCited⟩
  }
  exact ⟨rfl, cert⟩

end BEDC.Derived.ClaimRegistryLayerUp.TasteGate
