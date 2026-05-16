import BEDC.Derived.RealityConstrainedMethodologyLedgerUp.TasteGate
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.RealityConstrainedMethodologyLedgerUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def RealityConstrainedMethodologyLedgerCarrier [AskSetup] [PackageSetup]
    (X A O T I S D U F H C Q N : BHist) (bundle : ProbeBundle ProbeName) (pkg : Pkg) :
    Prop :=
  UnaryHistory X ∧ UnaryHistory A ∧ UnaryHistory O ∧ UnaryHistory T ∧ UnaryHistory I ∧
    UnaryHistory S ∧ UnaryHistory D ∧ UnaryHistory U ∧ UnaryHistory F ∧
      hsame H (append S D) ∧ Cont S D U ∧ Cont U F C ∧ Cont C Q N ∧
        PkgSig bundle Q pkg

theorem RealityConstrainedMethodologyLedgerCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {X A O T I S D U F H C Q N : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RealityConstrainedMethodologyLedgerCarrier X A O T I S D U F H C Q N bundle pkg ->
      SemanticNameCert
          (fun row : BHist =>
            RealityConstrainedMethodologyLedgerCarrier X A O T I S D U F H C Q row
              bundle pkg ∧ hsame row N)
          (fun row : BHist => hsame row N ∧ PkgSig bundle Q pkg)
          (fun row : BHist => hsame row N ∧ Cont C Q row)
          hsame ∧
        Cont S D U ∧ Cont U F C ∧ Cont C Q N ∧ PkgSig bundle Q pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro carrier
  rcases carrier with
    ⟨xUnary, aUnary, oUnary, tUnary, iUnary, sUnary, dUnary, uUnary, fUnary, sameH,
      scopeRefusalUpgrade, upgradeFailureConsumer, consumerProvenanceName, pkgSig⟩
  have carrierPacket :
      RealityConstrainedMethodologyLedgerCarrier X A O T I S D U F H C Q N bundle pkg :=
    ⟨xUnary, aUnary, oUnary, tUnary, iUnary, sUnary, dUnary, uUnary, fUnary, sameH,
      scopeRefusalUpgrade, upgradeFailureConsumer, consumerProvenanceName, pkgSig⟩
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            RealityConstrainedMethodologyLedgerCarrier X A O T I S D U F H C Q row
              bundle pkg ∧ hsame row N)
          (fun row : BHist => hsame row N ∧ PkgSig bundle Q pkg)
          (fun row : BHist => hsame row N ∧ Cont C Q row)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro N (And.intro carrierPacket (hsame_refl N))
        equiv_refl := by
          intro row _source
          exact hsame_refl row
        equiv_symm := by
          intro row row' same
          exact hsame_symm same
        equiv_trans := by
          intro row row' row'' sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro row row' same source
          rcases source with ⟨sourceCarrier, sourceSameName⟩
          rcases sourceCarrier with
            ⟨sourceX, sourceA, sourceO, sourceT, sourceI, sourceS, sourceD, sourceU,
              sourceF, sourceH, sourceSDU, sourceUFC, sourceCQN, sourcePkg⟩
          exact And.intro
            ⟨sourceX, sourceA, sourceO, sourceT, sourceI, sourceS, sourceD, sourceU,
              sourceF, sourceH, sourceSDU, sourceUFC,
              hsame_trans (hsame_symm same) sourceCQN, sourcePkg⟩
            (hsame_trans (hsame_symm same) sourceSameName)
      }
      pattern_sound := by
        intro row source
        exact And.intro source.right pkgSig
      ledger_sound := by
        intro row source
        cases source.right
        exact And.intro (hsame_refl N) consumerProvenanceName
    }
  exact
    ⟨cert, scopeRefusalUpgrade, upgradeFailureConsumer, consumerProvenanceName, pkgSig⟩

end BEDC.Derived.RealityConstrainedMethodologyLedgerUp
