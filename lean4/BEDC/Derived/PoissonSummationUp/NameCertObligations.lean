import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PoissonSummationUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem PoissonSummationNamecertObligations [AskSetup] [PackageSetup]
    {L F D S R H C P N observed : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory L →
      UnaryHistory F →
        UnaryHistory D →
          UnaryHistory S →
            Cont L F observed →
              Cont F D observed →
                Cont D S observed →
                  PkgSig bundle P pkg →
                    PkgSig bundle N pkg →
                      SemanticNameCert
                          (fun row : BHist => hsame row observed ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row L ∨ hsame row F ∨ hsame row D ∨ hsame row S ∨
                              hsame row R ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                                hsame row N ∨ hsame row observed)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont L F observed ∧
                              Cont F D observed ∧ Cont D S observed ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧
                        UnaryHistory observed := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro latticeUnary fourierUnary distributionUnary summationUnary latticeFourierObserved
    fourierDistributionObserved distributionSummationObserved provenancePkg namePkg
  have observedUnary : UnaryHistory observed :=
    unary_cont_closed latticeUnary fourierUnary latticeFourierObserved
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro observed ⟨hsame_refl observed, observedUnary⟩
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
        exact source.left
      ledger_sound := by
        intro _row source
        exact
          ⟨source.right, latticeFourierObserved, fourierDistributionObserved,
            distributionSummationObserved, provenancePkg, namePkg⟩
    }
  · exact observedUnary

end BEDC.Derived.PoissonSummationUp
