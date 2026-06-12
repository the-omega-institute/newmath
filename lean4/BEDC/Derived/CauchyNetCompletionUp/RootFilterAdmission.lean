import BEDC.Derived.CauchyNetCompletionUp.MooreSmithHandoff

namespace BEDC.Derived.CauchyNetCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyNetCompletionRootFilterAdmission [AskSetup] [PackageSetup]
    {D W Q M U S R A H C P N rootRead admittedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyNetCompletionCarrier D W Q M U S R A H C P N bundle pkg →
      Cont D W rootRead →
        Cont rootRead Q admittedRead →
          PkgSig bundle P pkg →
            SemanticNameCert
                (fun row : BHist => hsame row admittedRead ∧ UnaryHistory row)
                (fun row : BHist =>
                  hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row admittedRead)
                (fun row : BHist =>
                  UnaryHistory row ∧ Cont D W rootRead ∧
                    Cont rootRead Q admittedRead ∧ PkgSig bundle P pkg)
                hsame ∧
              UnaryHistory rootRead ∧ UnaryHistory admittedRead := by
  -- BEDC touchpoint anchor: CauchyNetCompletionCarrier BHist Cont ProbeBundle PkgSig SemanticNameCert hsame UnaryHistory
  intro carrier rootRoute admittedRoute provenancePkg
  obtain ⟨unaryD, unaryW, unaryQ, _unaryM, _unaryU, _unaryS, _unaryR, _unaryA,
    _unaryH, _unaryC, _unaryP, _unaryN, _carrierRoot, _carrierMoore, _carrierUniform,
      _carrierSeal, _carrierPkgP, _carrierPkgN⟩ := carrier
  have rootUnary : UnaryHistory rootRead :=
    unary_cont_closed unaryD unaryW rootRoute
  have admittedUnary : UnaryHistory admittedRead :=
    unary_cont_closed rootUnary unaryQ admittedRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row admittedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row D ∨ hsame row W ∨ hsame row Q ∨ hsame row admittedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont D W rootRead ∧ Cont rootRead Q admittedRead ∧
              PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro admittedRead ⟨hsame_refl admittedRead, admittedUnary⟩
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
      exact Or.inr (Or.inr (Or.inr source.left))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, rootRoute, admittedRoute, provenancePkg⟩
  }
  exact ⟨cert, rootUnary, admittedUnary⟩

end BEDC.Derived.CauchyNetCompletionUp
