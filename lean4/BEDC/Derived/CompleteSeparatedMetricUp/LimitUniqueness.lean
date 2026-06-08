import BEDC.Derived.CompleteSeparatedMetricUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.CompleteSeparatedMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem CompleteSeparatedMetricLimitUniqueness [AskSetup] [PackageSetup]
    {X C S E R H K P N completionRead zeroRead separatedRead replayRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    completeSeparatedMetricToEventFlow (CompleteSeparatedMetricUp.mk X C S E R H K P N) =
        [completeSeparatedMetricEncodeBHist X, completeSeparatedMetricEncodeBHist C,
          completeSeparatedMetricEncodeBHist S, completeSeparatedMetricEncodeBHist E,
          completeSeparatedMetricEncodeBHist R, completeSeparatedMetricEncodeBHist H,
          completeSeparatedMetricEncodeBHist K, completeSeparatedMetricEncodeBHist P,
          completeSeparatedMetricEncodeBHist N] ->
      Cont X C completionRead ->
        Cont E R zeroRead ->
          Cont S R separatedRead ->
            Cont H K replayRead ->
              PkgSig bundle P pkg ->
                PkgSig bundle N pkg ->
                  SemanticNameCert
                    (fun row : BHist => hsame row separatedRead ∧ Cont S R separatedRead)
                    (fun row : BHist =>
                      hsame row X ∨ hsame row C ∨ hsame row S ∨ hsame row E ∨
                        hsame row R ∨ Cont H K replayRead)
                    (fun row : BHist =>
                      hsame row separatedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                    hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows _completionRoute _zeroRoute separatedRoute replayRoute provenancePkg namePkg
  cases fieldRows
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro separatedRead (And.intro (hsame_refl separatedRead) separatedRoute)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _row' _row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact And.intro (hsame_trans (hsame_symm sameRows) source.left) source.right
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr replayRoute))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg namePkg)
  }

end BEDC.Derived.CompleteSeparatedMetricUp
