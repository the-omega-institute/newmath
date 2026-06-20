import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.PointwiseStreamMetricUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def PointwiseStreamMetricCarrier [AskSetup] [PackageSetup]
    (S W D R E M H C P N : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg PkgSig UnaryHistory
  UnaryHistory S ∧ UnaryHistory W ∧ UnaryHistory D ∧ UnaryHistory R ∧
    UnaryHistory E ∧ UnaryHistory M ∧ UnaryHistory H ∧ UnaryHistory C ∧
      UnaryHistory P ∧ UnaryHistory N ∧ PkgSig bundle P pkg ∧ PkgSig bundle N pkg

theorem PointwiseStreamMetricPointwiseClassifier [AskSetup] [PackageSetup]
    {S W D R E M H C P N windowRead toleranceRead readbackRead sealRead metricRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    PointwiseStreamMetricCarrier S W D R E M H C P N bundle pkg →
      Cont S W windowRead →
        Cont windowRead D toleranceRead →
          Cont toleranceRead R readbackRead →
            Cont readbackRead E sealRead →
              Cont sealRead M metricRead →
                PkgSig bundle P pkg →
                  PkgSig bundle metricRead pkg →
                    SemanticNameCert
                        (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
                        (fun row : BHist =>
                          hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨
                            hsame row E ∨ hsame row M ∨ hsame row metricRead)
                        (fun row : BHist =>
                          UnaryHistory row ∧ Cont S W windowRead ∧
                            Cont windowRead D toleranceRead ∧
                              Cont toleranceRead R readbackRead ∧
                                Cont readbackRead E sealRead ∧
                                  Cont sealRead M metricRead ∧ PkgSig bundle P pkg ∧
                                    PkgSig bundle metricRead pkg)
                        hsame ∧
                      UnaryHistory windowRead ∧ UnaryHistory toleranceRead ∧
                        UnaryHistory readbackRead ∧ UnaryHistory sealRead ∧
                          UnaryHistory metricRead := by
  -- BEDC touchpoint anchor: BHist Cont ProbeBundle PkgSig hsame SemanticNameCert
  intro carrier windowRoute toleranceRoute readbackRoute sealRoute metricRoute provenancePkg
    metricPkg
  obtain ⟨unaryS, unaryW, unaryD, unaryR, unaryE, unaryM, _unaryH, _unaryC, _unaryP,
    _unaryN, _carrierPkg, _carrierName⟩ := carrier
  have windowUnary : UnaryHistory windowRead := unary_cont_closed unaryS unaryW windowRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed windowUnary unaryD toleranceRoute
  have readbackUnary : UnaryHistory readbackRead :=
    unary_cont_closed toleranceUnary unaryR readbackRoute
  have sealUnary : UnaryHistory sealRead := unary_cont_closed readbackUnary unaryE sealRoute
  have metricUnary : UnaryHistory metricRead := unary_cont_closed sealUnary unaryM metricRoute
  have sourceMetric :
      (fun row : BHist => hsame row metricRead ∧ UnaryHistory row) metricRead := by
    exact ⟨hsame_refl metricRead, metricUnary⟩
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row metricRead ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row S ∨ hsame row W ∨ hsame row D ∨ hsame row R ∨ hsame row E ∨
              hsame row M ∨ hsame row metricRead)
          (fun row : BHist =>
            UnaryHistory row ∧ Cont S W windowRead ∧ Cont windowRead D toleranceRead ∧
              Cont toleranceRead R readbackRead ∧ Cont readbackRead E sealRead ∧
                Cont sealRead M metricRead ∧ PkgSig bundle P pkg ∧
                  PkgSig bundle metricRead pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro metricRead sourceMetric
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
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr source.left)))))
    ledger_sound := by
      intro _row source
      exact
        ⟨source.right, windowRoute, toleranceRoute, readbackRoute, sealRoute, metricRoute,
          provenancePkg, metricPkg⟩
  }
  exact ⟨cert, windowUnary, toleranceUnary, readbackUnary, sealUnary, metricUnary⟩

end BEDC.Derived.PointwiseStreamMetricUp
