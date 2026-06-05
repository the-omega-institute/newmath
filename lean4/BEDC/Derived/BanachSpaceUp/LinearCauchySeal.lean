import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.BanachSpaceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem BanachSpaceCarrier_linear_cauchy_seal [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L cauchyRead completionRead toleranceRead sealRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    (UnaryHistory V ∧ UnaryHistory N ∧ UnaryHistory M ∧ UnaryHistory Q ∧
        UnaryHistory S ∧ UnaryHistory R ∧ UnaryHistory E ∧ UnaryHistory Z ∧
          UnaryHistory H ∧ UnaryHistory C ∧ UnaryHistory P ∧ UnaryHistory L ∧
            PkgSig bundle P pkg) →
      Cont V N M →
        Cont M Q cauchyRead →
          Cont cauchyRead S completionRead →
            Cont completionRead R toleranceRead →
              Cont toleranceRead E sealRead →
                PkgSig bundle L pkg →
                  SemanticNameCert
                      (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
                      (fun row : BHist =>
                        hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨
                          hsame row S ∨ hsame row R ∨ hsame row E ∨ hsame row sealRead)
                      (fun row : BHist =>
                        UnaryHistory row ∧ Cont M Q cauchyRead ∧
                          Cont cauchyRead S completionRead ∧
                            Cont completionRead R toleranceRead ∧
                              Cont toleranceRead E sealRead ∧ PkgSig bundle L pkg)
                      hsame ∧
                    UnaryHistory cauchyRead ∧ UnaryHistory completionRead ∧
                      UnaryHistory toleranceRead ∧ UnaryHistory sealRead := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont SemanticNameCert hsame UnaryHistory
  intro carrierRows vectorMetricRoute cauchyRoute completionRoute toleranceRoute sealRoute
    localPkg
  have vUnary : UnaryHistory V := carrierRows.left
  have nUnary : UnaryHistory N := carrierRows.right.left
  have qUnary : UnaryHistory Q := carrierRows.right.right.right.left
  have sUnary : UnaryHistory S := carrierRows.right.right.right.right.left
  have rUnary : UnaryHistory R := carrierRows.right.right.right.right.right.left
  have eUnary : UnaryHistory E := carrierRows.right.right.right.right.right.right.left
  have metricUnary : UnaryHistory M :=
    unary_cont_closed vUnary nUnary vectorMetricRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed metricUnary qUnary cauchyRoute
  have completionUnary : UnaryHistory completionRead :=
    unary_cont_closed cauchyUnary sUnary completionRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed completionUnary rUnary toleranceRoute
  have sealUnary : UnaryHistory sealRead :=
    unary_cont_closed toleranceUnary eUnary sealRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row sealRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row sealRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont M Q cauchyRead ∧ Cont cauchyRead S completionRead ∧
              Cont completionRead R toleranceRead ∧ Cont toleranceRead E sealRead ∧
                PkgSig bundle L pkg)
          hsame := {
    core := {
      carrier_inhabited :=
        Exists.intro sealRead ⟨hsame_refl sealRead, sealUnary⟩
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left))))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, cauchyRoute, completionRoute, toleranceRoute, sealRoute,
          localPkg⟩
  }
  exact ⟨cert, cauchyUnary, completionUnary, toleranceUnary, sealUnary⟩

end BEDC.Derived.BanachSpaceUp
