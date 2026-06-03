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

theorem BolzanoWeierstrassCarrier_root_obligation_package [AskSetup] [PackageSetup]
    {S K R Q E H C P N sourceNet regseqWindow clusterSeal rootSurface : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    BolzanoWeierstrassCarrier S K R Q E H C P N bundle pkg ->
      Cont S K sourceNet ->
        Cont sourceNet Q regseqWindow ->
          Cont regseqWindow E clusterSeal ->
            Cont sourceNet clusterSeal rootSurface ->
              PkgSig bundle rootSurface pkg ->
                SemanticNameCert
                    (fun row : BHist => hsame row rootSurface ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨
                        hsame row E ∨ hsame row H ∨ hsame row C ∨ hsame row P ∨
                          hsame row N ∨ hsame row rootSurface)
                    (fun row : BHist =>
                      UnaryHistory row ∧ PkgSig bundle rootSurface pkg ∧
                        Cont sourceNet clusterSeal rootSurface)
                    hsame ∧
                  UnaryHistory rootSurface := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory
  intro carrier sourceRoute regseqRoute clusterRoute rootRoute rootPkg
  obtain ⟨SUnary, KUnary, _RUnary, QUnary, EUnary, _HUnary, _CUnary, _PUnary,
    _NUnary, _sourceIntervalRoute, _readbackSealRoute, _transportReplayRoute,
    _carrierPkg⟩ := carrier
  have sourceNetUnary : UnaryHistory sourceNet :=
    unary_cont_closed SUnary KUnary sourceRoute
  have regseqWindowUnary : UnaryHistory regseqWindow :=
    unary_cont_closed sourceNetUnary QUnary regseqRoute
  have clusterSealUnary : UnaryHistory clusterSeal :=
    unary_cont_closed regseqWindowUnary EUnary clusterRoute
  have rootUnary : UnaryHistory rootSurface :=
    unary_cont_closed sourceNetUnary clusterSealUnary rootRoute
  have sourceRoot :
      (fun row : BHist => hsame row rootSurface ∧ UnaryHistory row) rootSurface := by
    exact ⟨hsame_refl rootSurface, rootUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row rootSurface ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row K ∨ hsame row R ∨ hsame row Q ∨ hsame row E ∨
              hsame row H ∨ hsame row C ∨ hsame row P ∨ hsame row N ∨
                hsame row rootSurface)
          (fun row : BHist =>
            UnaryHistory row ∧ PkgSig bundle rootSurface pkg ∧
              Cont sourceNet clusterSeal rootSurface)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro rootSurface sourceRoot
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
      exact
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr source.left))))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rootPkg, rootRoute⟩
  }
  exact ⟨cert, rootUnary⟩

end BEDC.Derived.BolzanoWeierstrassUp
