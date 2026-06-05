import BEDC.Derived.KuratowskiClusterSetUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.KuratowskiClusterSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package

theorem KuratowskiClusterSetNetFilterHandoff [AskSetup] [PackageSetup]
    {S F Kh Km C M B X R E T U P N sourceFrontier boundaryRead supportRead hitRead sealRead
      replayRead : BHist} {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    TasteGate.kuratowskiClusterSetFields
        (TasteGate.KuratowskiClusterSetUp.mk S F Kh Km C M B X R E T U P N) =
        [S, F, Kh, Km, C, M, B, X, R, E, T, U, P, N] ->
      Cont S F sourceFrontier ->
        Cont Kh Km boundaryRead ->
          Cont C M supportRead ->
            Cont B X hitRead ->
              Cont R E sealRead ->
                Cont T U replayRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                        (fun row : BHist => hsame row replayRead ∧ Cont T U replayRead)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row F ∨ hsame row Kh ∨ hsame row Km ∨
                            hsame row C ∨ hsame row M ∨ hsame row B ∨ hsame row X ∨
                              hsame row R ∨ hsame row E ∨ Cont T U replayRead)
                        (fun row : BHist =>
                          hsame row replayRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                        hsame := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert
  intro fieldRows _sourceFrontier _boundaryRead _supportRead _hitRead _sealRead replayRoute
    provenancePkg namePkg
  cases fieldRows
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro replayRead (And.intro (hsame_refl replayRead) replayRoute)
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
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inr source.right)))))))))
    ledger_sound := by
      intro _row source
      exact And.intro source.left (And.intro provenancePkg namePkg)
  }

end BEDC.Derived.KuratowskiClusterSetUp
