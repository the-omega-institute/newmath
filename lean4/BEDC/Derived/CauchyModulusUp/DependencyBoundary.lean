import BEDC.Derived.CauchyModulusUp

namespace BEDC.Derived.CauchyModulusUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem CauchyModulusCarrier_dependency_boundary [AskSetup] [PackageSetup]
    {precision threshold tolerance schedule consumption provenance window endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyModulusCarrier precision threshold tolerance schedule consumption provenance window
        bundle pkg ->
      Cont window threshold endpoint ->
        PkgSig bundle endpoint pkg ->
          SemanticNameCert (fun h : BHist => hsame h endpoint)
              (fun h : BHist => hsame h endpoint ∧ UnaryHistory h)
              (fun h : BHist =>
                hsame h endpoint ∧ Cont precision threshold consumption ∧
                  Cont tolerance schedule provenance ∧ Cont consumption provenance window)
              hsame ∧
            UnaryHistory precision ∧ UnaryHistory threshold ∧ UnaryHistory tolerance ∧
              UnaryHistory schedule ∧ Cont precision threshold consumption ∧
                Cont tolerance schedule provenance ∧ Cont consumption provenance window ∧
                  PkgSig bundle endpoint pkg := by
  intro carrier endpointRow endpointPkg
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed carrier.right.right.right.right.right.right.left
      carrier.right.left endpointRow
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint ∧ UnaryHistory h)
          (fun h : BHist =>
            hsame h endpoint ∧ Cont precision threshold consumption ∧
              Cont tolerance schedule provenance ∧ Cont consumption provenance window)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint (hsame_refl endpoint)
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' same
        exact hsame_symm same
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows sourceRow
        exact hsame_trans (hsame_symm sameRows) sourceRow
    }
    pattern_sound := by
      intro row sourceRow
      exact And.intro sourceRow (unary_transport endpointUnary (hsame_symm sourceRow))
    ledger_sound := by
      intro _row sourceRow
      exact And.intro sourceRow
        (And.intro carrier.right.right.right.right.right.right.right.left
          (And.intro carrier.right.right.right.right.right.right.right.right.left
            carrier.right.right.right.right.right.right.right.right.right.left))
  }
  exact And.intro cert
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro carrier.right.right.right.right.right.right.right.left
              (And.intro carrier.right.right.right.right.right.right.right.right.left
                (And.intro carrier.right.right.right.right.right.right.right.right.right.left
                  endpointPkg)))))))

end BEDC.Derived.CauchyModulusUp
