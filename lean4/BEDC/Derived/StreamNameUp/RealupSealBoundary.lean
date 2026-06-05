import BEDC.Derived.StreamNameUp
import BEDC.FKernel.Ask
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package

namespace BEDC.Derived.StreamNameUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem StreamnameRealupSealBoundary [AskSetup] [PackageSetup]
    {window regseqRead pointwiseSeal bundleRows membershipRows observationRows realSeal : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory window ->
      UnaryHistory regseqRead ->
        UnaryHistory pointwiseSeal ->
          UnaryHistory bundleRows ->
            UnaryHistory membershipRows ->
              UnaryHistory observationRows ->
                Cont window regseqRead pointwiseSeal ->
                  Cont pointwiseSeal bundleRows membershipRows ->
                    Cont membershipRows observationRows realSeal ->
                      PkgSig bundle realSeal pkg ->
                        SemanticNameCert
                            (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row window ∨ hsame row regseqRead ∨
                                hsame row pointwiseSeal ∨ hsame row bundleRows ∨
                                  hsame row membershipRows ∨ hsame row realSeal)
                            (fun _row : BHist =>
                              Cont window regseqRead pointwiseSeal ∧
                                Cont pointwiseSeal bundleRows membershipRows ∧
                                  Cont membershipRows observationRows realSeal ∧
                                    PkgSig bundle realSeal pkg)
                            hsame ∧ UnaryHistory realSeal := by
  -- BEDC touchpoint anchor: BHist UnaryHistory Cont ProbeBundle PkgSig SemanticNameCert
  intro _windowUnary _regseqUnary pointwiseSealUnary bundleRowsUnary _membershipRowsUnary
    observationRowsUnary windowPointwise pointwiseMembership membershipReal pkgRow
  have membershipRowsUnaryFromRoute : UnaryHistory membershipRows :=
    unary_cont_closed pointwiseSealUnary bundleRowsUnary pointwiseMembership
  have realSealUnary : UnaryHistory realSeal :=
    unary_cont_closed membershipRowsUnaryFromRoute observationRowsUnary membershipReal
  have cert :
      SemanticNameCert
        (fun row : BHist => hsame row realSeal ∧ UnaryHistory row)
        (fun row : BHist =>
          hsame row window ∨ hsame row regseqRead ∨ hsame row pointwiseSeal ∨
            hsame row bundleRows ∨ hsame row membershipRows ∨ hsame row realSeal)
        (fun _row : BHist =>
          Cont window regseqRead pointwiseSeal ∧ Cont pointwiseSeal bundleRows membershipRows ∧
            Cont membershipRows observationRows realSeal ∧ PkgSig bundle realSeal pkg)
        hsame := {
    core := {
      carrier_inhabited := Exists.intro realSeal ⟨hsame_refl realSeal, realSealUnary⟩
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro _row _row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro _row _middle _row' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro _row _row' sameRows source
        exact
          ⟨hsame_trans (hsame_symm sameRows) source.left,
            unary_transport source.right sameRows⟩
    }
    pattern_sound := by
      intro _row source
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row _source
      exact ⟨windowPointwise, pointwiseMembership, membershipReal, pkgRow⟩
  }
  exact ⟨cert, realSealUnary⟩

end BEDC.Derived.StreamNameUp
