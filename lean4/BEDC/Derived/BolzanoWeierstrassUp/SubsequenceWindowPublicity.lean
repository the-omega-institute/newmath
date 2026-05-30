import BEDC.Derived.BolzanoWeierstrassUp.FiniteSubsequenceObligations
import BEDC.FKernel.NameCert

namespace BEDC.Derived.BolzanoWeierstrassUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BolzanoWeierstrassSubsequenceWindowPublicity [AskSetup] [PackageSetup]
    {S K R Q E H C P N selector cluster publicWindow : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K selector ->
        Cont selector R Q ->
          Cont Q E cluster ->
            Cont cluster H publicWindow ->
              PkgSig bundle publicWindow pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row publicWindow ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                        hsame row E ∨ Cont cluster H publicWindow)
                    (fun row : BHist =>
                      PkgSig bundle publicWindow pkg ∧ hsame row publicWindow)
                    hsame ∧
                  UnaryHistory selector ∧ UnaryHistory cluster ∧
                    UnaryHistory publicWindow ∧ Cont S K selector ∧
                      Cont selector R Q ∧ Cont Q E cluster ∧
                        Cont cluster H publicWindow ∧ PkgSig bundle P pkg ∧
                          PkgSig bundle publicWindow pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier selectorRoute selectorReadback clusterRoute publicRoute publicPkg
  obtain ⟨SUnary, KUnary, RUnary, QUnary, EUnary, HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    carrierPkg⟩ := carrier
  have selectorUnary : UnaryHistory selector :=
    unary_cont_closed SUnary KUnary selectorRoute
  have clusterUnary : UnaryHistory cluster :=
    unary_cont_closed QUnary EUnary clusterRoute
  have publicUnary : UnaryHistory publicWindow :=
    unary_cont_closed clusterUnary HUnary publicRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row publicWindow ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
              hsame row E ∨ Cont cluster H publicWindow)
          (fun row : BHist => PkgSig bundle publicWindow pkg ∧ hsame row publicWindow)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro publicWindow
        ⟨hsame_refl publicWindow, publicUnary⟩
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
        intro _row other sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row _source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr publicRoute))))
    ledger_sound := by
      intro _row source
      exact ⟨publicPkg, source.left⟩
  }
  exact
    ⟨cert, selectorUnary, clusterUnary, publicUnary, selectorRoute, selectorReadback,
      clusterRoute, publicRoute, carrierPkg, publicPkg⟩

end BEDC.Derived.BolzanoWeierstrassUp
