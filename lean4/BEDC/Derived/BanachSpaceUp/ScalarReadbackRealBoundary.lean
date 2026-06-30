import BEDC.Derived.BanachSpaceUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
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

theorem BanachSpaceScalarReadbackRealBoundary [AskSetup] [PackageSetup]
    {V N M Q S R E Z H C P L normRead metricRead cauchyRead toleranceRead
      realSealRead scalarName : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UnaryHistory V → UnaryHistory N → UnaryHistory M → UnaryHistory Q →
      UnaryHistory S → UnaryHistory R → UnaryHistory E → UnaryHistory L →
        Cont V N normRead →
          Cont normRead M metricRead →
            Cont Q S cauchyRead →
              Cont cauchyRead R toleranceRead →
                Cont toleranceRead E realSealRead →
                  Cont realSealRead L scalarName →
                    PkgSig bundle P pkg →
                      PkgSig bundle scalarName pkg →
                        SemanticNameCert
                            (fun row : BHist => hsame row scalarName ∧ UnaryHistory row)
                            (fun row : BHist =>
                              hsame row V ∨ hsame row N ∨ hsame row M ∨
                                hsame row Q ∨ hsame row S ∨ hsame row R ∨
                                  hsame row E ∨ hsame row L ∨ hsame row scalarName)
                            (fun row : BHist =>
                              hsame row scalarName ∧ PkgSig bundle scalarName pkg)
                            hsame ∧
                          UnaryHistory normRead ∧ UnaryHistory metricRead ∧
                            UnaryHistory cauchyRead ∧ UnaryHistory toleranceRead ∧
                              UnaryHistory realSealRead ∧ UnaryHistory scalarName := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame SemanticNameCert UnaryHistory BanachSpaceUp
  intro unaryV unaryN unaryM unaryQ unaryS unaryR unaryE unaryL
  intro normRoute metricRoute cauchyRoute toleranceRoute realSealRoute scalarRoute
  intro _provenancePkg scalarPkg
  have normUnary : UnaryHistory normRead :=
    unary_cont_closed unaryV unaryN normRoute
  have metricUnary : UnaryHistory metricRead :=
    unary_cont_closed normUnary unaryM metricRoute
  have cauchyUnary : UnaryHistory cauchyRead :=
    unary_cont_closed unaryQ unaryS cauchyRoute
  have toleranceUnary : UnaryHistory toleranceRead :=
    unary_cont_closed cauchyUnary unaryR toleranceRoute
  have realSealUnary : UnaryHistory realSealRead :=
    unary_cont_closed toleranceUnary unaryE realSealRoute
  have scalarUnary : UnaryHistory scalarName :=
    unary_cont_closed realSealUnary unaryL scalarRoute
  have cert :
      SemanticNameCert
          (fun row : BHist => hsame row scalarName ∧ UnaryHistory row)
          (fun row : BHist =>
            hsame row V ∨ hsame row N ∨ hsame row M ∨ hsame row Q ∨ hsame row S ∨
              hsame row R ∨ hsame row E ∨ hsame row L ∨ hsame row scalarName)
          (fun row : BHist => hsame row scalarName ∧ PkgSig bundle scalarName pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro scalarName ⟨hsame_refl scalarName, scalarUnary⟩
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
        Or.inr
          (Or.inr
            (Or.inr
              (Or.inr
                (Or.inr
                  (Or.inr
                    (Or.inr
                      (Or.inr source.left)))))))
    ledger_sound := by
      intro _row source
      exact ⟨source.left, scalarPkg⟩
  }
  exact
    ⟨cert, normUnary, metricUnary, cauchyUnary, toleranceUnary, realSealUnary,
      scalarUnary⟩

end BEDC.Derived.BanachSpaceUp
