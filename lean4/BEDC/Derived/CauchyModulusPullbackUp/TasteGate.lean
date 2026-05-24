import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Mark
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.Meta.TasteGate

namespace BEDC.Derived.CauchyModulusPullbackUp

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

inductive CauchyModulusPullbackUp : Type where
  | mk
      (source reindexed route modulus dyadic readback realSeal transport replay provenance name :
        BHist) :
      CauchyModulusPullbackUp
  deriving DecidableEq

def cauchyModulusPullbackEncodeBHist : BHist → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | BHist.Empty => []
  | BHist.e0 h => BMark.b0 :: cauchyModulusPullbackEncodeBHist h
  | BHist.e1 h => BMark.b1 :: cauchyModulusPullbackEncodeBHist h

def cauchyModulusPullbackDecodeBHist : RawEvent → BHist
  -- BEDC touchpoint anchor: BHist BMark
  | [] => BHist.Empty
  | BMark.b0 :: tail => BHist.e0 (cauchyModulusPullbackDecodeBHist tail)
  | BMark.b1 :: tail => BHist.e1 (cauchyModulusPullbackDecodeBHist tail)

private theorem CauchyModulusPullback_decode_encode :
    ∀ h : BHist, cauchyModulusPullbackDecodeBHist
      (cauchyModulusPullbackEncodeBHist h) = h := by
  -- BEDC touchpoint anchor: BHist BMark
  intro h
  induction h with
  | Empty => rfl
  | e0 h ih => exact congrArg BHist.e0 ih
  | e1 h ih => exact congrArg BHist.e1 ih

def cauchyModulusPullbackFields : CauchyModulusPullbackUp → List BHist
  -- BEDC touchpoint anchor: BHist BMark
  | CauchyModulusPullbackUp.mk source reindexed route modulus dyadic readback realSeal
      transport replay provenance name =>
      [source, reindexed, route, modulus, dyadic, readback, realSeal, transport, replay,
        provenance, name]

def cauchyModulusPullbackToEventFlow : CauchyModulusPullbackUp → EventFlow
  -- BEDC touchpoint anchor: BHist BMark
  | x => (cauchyModulusPullbackFields x).map cauchyModulusPullbackEncodeBHist

private def cauchyModulusPullbackEventAt : Nat → EventFlow → RawEvent
  -- BEDC touchpoint anchor: BHist BMark
  | Nat.zero, [] => []
  | Nat.zero, event :: _rest => event
  | Nat.succ _index, [] => []
  | Nat.succ index, _event :: rest => cauchyModulusPullbackEventAt index rest

def cauchyModulusPullbackFromEventFlow (ef : EventFlow) :
    Option CauchyModulusPullbackUp :=
  -- BEDC touchpoint anchor: BHist BMark
  some
    (CauchyModulusPullbackUp.mk
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 0 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 1 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 2 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 3 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 4 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 5 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 6 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 7 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 8 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 9 ef))
      (cauchyModulusPullbackDecodeBHist (cauchyModulusPullbackEventAt 10 ef)))

private theorem CauchyModulusPullback_round_trip (x : CauchyModulusPullbackUp) :
    cauchyModulusPullbackFromEventFlow (cauchyModulusPullbackToEventFlow x) = some x := by
  -- BEDC touchpoint anchor: BHist BMark
  cases x with
  | mk source reindexed route modulus dyadic readback realSeal transport replay provenance name =>
      change
        some
          (CauchyModulusPullbackUp.mk
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist source))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist reindexed))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist route))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist modulus))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist dyadic))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist readback))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist realSeal))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist transport))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist replay))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist provenance))
            (cauchyModulusPullbackDecodeBHist
              (cauchyModulusPullbackEncodeBHist name))) =
          some
            (CauchyModulusPullbackUp.mk source reindexed route modulus dyadic readback realSeal
              transport replay provenance name)
      rw [CauchyModulusPullback_decode_encode source,
        CauchyModulusPullback_decode_encode reindexed,
        CauchyModulusPullback_decode_encode route,
        CauchyModulusPullback_decode_encode modulus,
        CauchyModulusPullback_decode_encode dyadic,
        CauchyModulusPullback_decode_encode readback,
        CauchyModulusPullback_decode_encode realSeal,
        CauchyModulusPullback_decode_encode transport,
        CauchyModulusPullback_decode_encode replay,
        CauchyModulusPullback_decode_encode provenance,
        CauchyModulusPullback_decode_encode name]

private theorem CauchyModulusPullback_toEventFlow_injective {x y : CauchyModulusPullbackUp} :
    cauchyModulusPullbackToEventFlow x = cauchyModulusPullbackToEventFlow y → x = y := by
  -- BEDC touchpoint anchor: BHist BMark
  intro heq
  have hread :
      cauchyModulusPullbackFromEventFlow (cauchyModulusPullbackToEventFlow x) =
        cauchyModulusPullbackFromEventFlow (cauchyModulusPullbackToEventFlow y) :=
    congrArg cauchyModulusPullbackFromEventFlow heq
  exact Option.some.inj
    (Eq.trans (CauchyModulusPullback_round_trip x).symm
      (Eq.trans hread (CauchyModulusPullback_round_trip y)))

instance cauchyModulusPullbackBHistCarrier : BHistCarrier CauchyModulusPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  toEventFlow := cauchyModulusPullbackToEventFlow
  fromEventFlow := cauchyModulusPullbackFromEventFlow

instance cauchyModulusPullbackChapterTasteGate :
    ChapterTasteGate CauchyModulusPullbackUp where
  -- BEDC touchpoint anchor: BHist BMark
  round_trip := CauchyModulusPullback_round_trip
  layer_separation := by
    intro x y hxy heq
    exact hxy (CauchyModulusPullback_toEventFlow_injective heq)

def CauchyModulusPullbackCarrier [AskSetup] [PackageSetup]
    (source reindexed route modulus dyadic readback realSeal transport replay provenance name :
      BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig
  UnaryHistory source ∧ UnaryHistory reindexed ∧ UnaryHistory route ∧
    UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
      UnaryHistory realSeal ∧ UnaryHistory transport ∧ UnaryHistory replay ∧
        UnaryHistory provenance ∧ UnaryHistory name ∧
          Cont reindexed route transport ∧ Cont transport modulus replay ∧
            Cont replay dyadic readback ∧ Cont readback realSeal provenance ∧
              PkgSig bundle name pkg

theorem CauchyModulusPullbackCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source reindexed route modulus dyadic readback realSeal transport replay provenance name
      pulledThreshold : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusPullbackCarrier source reindexed route modulus dyadic readback realSeal
        transport replay provenance name bundle pkg →
      Cont reindexed route pulledThreshold →
        Cont pulledThreshold modulus dyadic →
          PkgSig bundle name pkg →
            UnaryHistory source ∧ UnaryHistory reindexed ∧ UnaryHistory route ∧
              UnaryHistory modulus ∧ UnaryHistory dyadic ∧ UnaryHistory readback ∧
                UnaryHistory realSeal ∧ UnaryHistory pulledThreshold ∧
                  Cont reindexed route pulledThreshold ∧ Cont pulledThreshold modulus dyadic ∧
                    PkgSig bundle name pkg ∧
                      SemanticNameCert
                        (fun row : BHist =>
                          hsame row source ∨ hsame row reindexed ∨
                            hsame row pulledThreshold ∨ hsame row realSeal)
                        (fun row : BHist =>
                          Cont reindexed route pulledThreshold ∧
                            (hsame row source ∨ hsame row reindexed ∨
                              hsame row pulledThreshold ∨ hsame row realSeal))
                        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist Cont UnaryHistory ProbeBundle Pkg PkgSig SemanticNameCert hsame
  intro carrier routePull thresholdPull pkgSig
  obtain ⟨sourceUnary, reindexedUnary, routeUnary, modulusUnary, dyadicUnary, readbackUnary,
    sealUnary, _transportUnary, _replayUnary, _provenanceUnary, _nameUnary, _carrierRoute,
    _carrierReplay, _carrierReadback, _carrierSeal, _carrierPkg⟩ := carrier
  have pulledUnary : UnaryHistory pulledThreshold :=
    unary_cont_closed reindexedUnary routeUnary routePull
  have cert :
      SemanticNameCert
        (fun row : BHist =>
          hsame row source ∨ hsame row reindexed ∨
            hsame row pulledThreshold ∨ hsame row realSeal)
        (fun row : BHist =>
          Cont reindexed route pulledThreshold ∧
            (hsame row source ∨ hsame row reindexed ∨
              hsame row pulledThreshold ∨ hsame row realSeal))
        (fun row : BHist => UnaryHistory row ∧ PkgSig bundle name pkg)
        hsame := by
    exact {
      core := {
        carrier_inhabited := Exists.intro source (Or.inl (hsame_refl source))
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
          intro _row _other same sourceSpec
          cases sourceSpec with
          | inl sameSource =>
              exact Or.inl (hsame_trans (hsame_symm same) sameSource)
          | inr rest =>
              cases rest with
              | inl sameReindexed =>
                  exact Or.inr (Or.inl (hsame_trans (hsame_symm same) sameReindexed))
              | inr rest =>
                  cases rest with
                  | inl samePulled =>
                      exact Or.inr
                        (Or.inr (Or.inl (hsame_trans (hsame_symm same) samePulled)))
                  | inr sameSeal =>
                      exact Or.inr
                        (Or.inr (Or.inr (hsame_trans (hsame_symm same) sameSeal)))
      }
      pattern_sound := by
        intro _row sourceSpec
        exact ⟨routePull, sourceSpec⟩
      ledger_sound := by
        intro row sourceSpec
        have rowUnary : UnaryHistory row := by
          cases sourceSpec with
          | inl sameSource =>
              exact unary_transport sourceUnary (hsame_symm sameSource)
          | inr rest =>
              cases rest with
              | inl sameReindexed =>
                  exact unary_transport reindexedUnary (hsame_symm sameReindexed)
              | inr rest =>
                  cases rest with
                  | inl samePulled =>
                      exact unary_transport pulledUnary (hsame_symm samePulled)
                  | inr sameSeal =>
                      exact unary_transport sealUnary (hsame_symm sameSeal)
        exact ⟨rowUnary, pkgSig⟩
    }
  exact
    ⟨sourceUnary, reindexedUnary, routeUnary, modulusUnary, dyadicUnary, readbackUnary,
      sealUnary, pulledUnary, routePull, thresholdPull, pkgSig, cert⟩

end BEDC.Derived.CauchyModulusPullbackUp
