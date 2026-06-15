import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.DyadicIntervalBisectionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem DyadicIntervalBisectionNamecertObligations [AskSetup] [PackageSetup]
    {L R M S W J H _C P _N midpoint branch nested replay named : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    Cont L R midpoint →
      Cont midpoint M branch →
        Cont S W nested →
          Cont J H replay →
            Cont replay P named →
              PkgSig bundle named pkg →
                SemanticNameCert
                    (fun row : BHist =>
                      hsame row named ∧ Cont replay P named ∧ PkgSig bundle named pkg)
                    (fun row : BHist =>
                      hsame row L ∨ hsame row R ∨ hsame row M ∨ hsame row S ∨
                        hsame row W ∨ hsame row J ∨ hsame row named)
                    (fun row : BHist => PkgSig bundle named pkg ∧ hsame row named)
                    hsame ∧
                  Cont L R midpoint ∧ Cont midpoint M branch ∧ Cont S W nested ∧
                    Cont J H replay ∧ Cont replay P named := by
  -- BEDC touchpoint anchor: BHist Cont hsame ProbeBundle Pkg PkgSig SemanticNameCert
  intro endpointRoute midpointRoute nestedRoute replayRoute namedRoute pkgNamed
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row named ∧ Cont replay P named ∧ PkgSig bundle named pkg)
          (fun row : BHist =>
            hsame row L ∨ hsame row R ∨ hsame row M ∨ hsame row S ∨ hsame row W ∨
              hsame row J ∨ hsame row named)
          (fun row : BHist => PkgSig bundle named pkg ∧ hsame row named)
          hsame := by
    exact {
      core := {
        carrier_inhabited :=
          Exists.intro named ⟨hsame_refl named, namedRoute, pkgNamed⟩
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
          intro _row _other sameRows sourceRow
          exact
            ⟨hsame_trans (hsame_symm sameRows) sourceRow.left,
              sourceRow.right.left,
              sourceRow.right.right⟩
      }
      pattern_sound := by
        intro _row sourceRow
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr sourceRow.left)))))
      ledger_sound := by
        intro _row sourceRow
        exact ⟨pkgNamed, sourceRow.left⟩
    }
  exact ⟨cert, endpointRoute, midpointRoute, nestedRoute, replayRoute, namedRoute⟩

end BEDC.Derived.DyadicIntervalBisectionUp
