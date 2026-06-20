import BEDC.Derived.RegularCauchyTailEstimateUp

namespace BEDC.Derived.RegularCauchyTailEstimateUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem RegularCauchyTailEstimateCarrier_window_triangle [AskSetup] [PackageSetup]
    {M W D R E H C P N firstRead secondRead combinedRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    RegularCauchyTailEstimateCarrier M W D R E H C P N bundle pkg →
      Cont W D firstRead →
        Cont firstRead R secondRead →
          Cont secondRead E combinedRead →
            hsame H (append C P) →
              PkgSig bundle P pkg →
                SemanticNameCert
                    (fun row : BHist => hsame row combinedRead ∧ UnaryHistory row)
                    (fun row : BHist =>
                      hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                        hsame row E ∨ hsame row combinedRead)
                    (fun row : BHist =>
                      UnaryHistory row ∧ Cont W D firstRead ∧
                        Cont firstRead R secondRead ∧ Cont secondRead E combinedRead ∧
                          hsame H (append C P) ∧ PkgSig bundle P pkg)
                    hsame ∧
                  UnaryHistory combinedRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont append hsame SemanticNameCert
  intro carrier routeFirst routeSecond routeCombined hstable provenance
  obtain ⟨_unaryM, unaryW, unaryD, unaryR, unaryE, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have firstUnary : UnaryHistory firstRead :=
    unary_cont_closed unaryW unaryD routeFirst
  have secondUnary : UnaryHistory secondRead :=
    unary_cont_closed firstUnary unaryR routeSecond
  have combinedUnary : UnaryHistory combinedRead :=
    unary_cont_closed secondUnary unaryE routeCombined
  have sourceCombined :
      (fun row : BHist => hsame row combinedRead ∧ UnaryHistory row) combinedRead := by
    exact ⟨hsame_refl combinedRead, combinedUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row combinedRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row M ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row combinedRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont W D firstRead ∧ Cont firstRead R secondRead ∧
              Cont secondRead E combinedRead ∧ hsame H (append C P) ∧
                PkgSig bundle P pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro combinedRead sourceCombined
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))
    ledger_sound := by
      intro _row source
      exact ⟨source.right, routeFirst, routeSecond, routeCombined, hstable, provenance⟩
  }
  exact ⟨cert, combinedUnary⟩

end BEDC.Derived.RegularCauchyTailEstimateUp
