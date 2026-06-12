import BEDC.Derived.ClosedTermSubstitutionBoundaryUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.ClosedtermsubstitutionboundaryUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem ClosedTermSubstitutionBoundaryClosedValuePreservation [AskSetup] [PackageSetup]
    {T V d Csrc Cval Q R L A H C P N valueRead substRead preservedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory Cval ->
      UnaryHistory R ->
        UnaryHistory L ->
          UnaryHistory N ->
            Cont Cval R valueRead ->
              Cont valueRead L substRead ->
                Cont substRead N preservedRead ->
                  PkgSig bundle P pkg ->
                    PkgSig bundle N pkg ->
                      SemanticNameCert
                          (fun row : BHist => hsame row preservedRead ∧ UnaryHistory row)
                          (fun row : BHist =>
                            hsame row Cval ∨ hsame row R ∨ hsame row L ∨ hsame row N ∨
                              hsame row preservedRead)
                          (fun row : BHist =>
                            UnaryHistory row ∧ Cont Cval R valueRead ∧
                              Cont valueRead L substRead ∧ Cont substRead N preservedRead ∧
                                PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
                          hsame ∧ UnaryHistory preservedRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle Pkg PkgSig SemanticNameCert hsame UnaryHistory
  intro cvalUnary rUnary lUnary nUnary valueRow substRow preservedRow provenancePkg localPkg
  have valueReadUnary : UnaryHistory valueRead :=
    unary_cont_closed cvalUnary rUnary valueRow
  have substReadUnary : UnaryHistory substRead :=
    unary_cont_closed valueReadUnary lUnary substRow
  have preservedUnary : UnaryHistory preservedRead :=
    unary_cont_closed substReadUnary nUnary preservedRow
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row preservedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row Cval ∨ hsame row R ∨ hsame row L ∨ hsame row N ∨
              hsame row preservedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont Cval R valueRead ∧ Cont valueRead L substRead ∧
              Cont substRead N preservedRead ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro preservedRead
        (And.intro (hsame_refl preservedRead) preservedUnary)
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
      exact Or.inr (Or.inr (Or.inr (Or.inr source.left)))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, valueRow, substRow, preservedRow, provenancePkg, localPkg⟩
  }
  exact ⟨cert, preservedUnary⟩

end BEDC.Derived.ClosedtermsubstitutionboundaryUp
