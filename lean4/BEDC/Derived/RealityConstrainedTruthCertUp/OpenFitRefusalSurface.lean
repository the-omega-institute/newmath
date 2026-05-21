import BEDC.Derived.RealityConstrainedTruthCertUp.TasteGate
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.RealityConstrainedTruthCertUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem RealityConstrainedTruthCertOpenFitRefusalSurface [AskSetup] [PackageSetup]
    (x : TasteGate.RealityConstrainedTruthCertUp)
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    exists S Sigma K T U D I L F N refusalMethodology l10Refusal : BHist,
      x = TasteGate.RealityConstrainedTruthCertUp.mk S Sigma K T U D I L F N /\
        TasteGate.realityConstrainedTruthCertFields x = [S, Sigma, K, T, U, D, I, L, F, N] /\
          Cont F L refusalMethodology /\
            Cont refusalMethodology N l10Refusal /\
              PkgSig bundle l10Refusal pkg ->
                SemanticNameCert
                  (fun row : BHist => hsame row l10Refusal)
                  (fun row : BHist =>
                    hsame row F \/ hsame row refusalMethodology \/ hsame row l10Refusal)
                  (fun row : BHist => hsame row l10Refusal /\ PkgSig bundle l10Refusal pkg)
                  hsame := by
  -- BEDC touchpoint anchor: BHist Cont PkgSig SemanticNameCert hsame
  cases x with
  | mk S Sigma K T U D I L F N =>
      let refusalMethodology := append F L
      let l10Refusal := append refusalMethodology N
      refine
        ⟨S, Sigma, K, T, U, D, I, L, F, N, refusalMethodology, l10Refusal, ?_⟩
      intro packet
      obtain ⟨_xFields, packet⟩ := packet
      obtain ⟨_fieldList, packet⟩ := packet
      obtain ⟨_openFit, packet⟩ := packet
      obtain ⟨_l10Route, l10Pkg⟩ := packet
      exact {
        core := {
          carrier_inhabited :=
            Exists.intro l10Refusal (hsame_refl l10Refusal)
          equiv_refl := by
            intro row _source
            exact hsame_refl row
          equiv_symm := by
            intro _row _row' same
            exact hsame_symm same
          equiv_trans := by
            intro _row _row' _row'' sameLeft sameRight
            exact hsame_trans sameLeft sameRight
          carrier_respects_equiv := by
            intro _row _row' same sourceRow
            exact hsame_trans (hsame_symm same) sourceRow
        }
        pattern_sound := by
          intro row sourceRow
          exact Or.inr (Or.inr sourceRow)
        ledger_sound := by
          intro row sourceRow
          exact And.intro sourceRow l10Pkg
      }

end BEDC.Derived.RealityConstrainedTruthCertUp
