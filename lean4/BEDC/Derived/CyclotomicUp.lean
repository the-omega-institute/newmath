import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CyclotomicUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CyclotomicRootCarrier [AskSetup] [PackageSetup]
    (numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory numField ∧ UnaryHistory exponent ∧ UnaryHistory polynomial ∧
    UnaryHistory splittingField ∧ UnaryHistory primitiveRoot ∧
      Cont numField splittingField provenance ∧ Cont exponent polynomial acceptance ∧
        Cont acceptance primitiveRoot ledger ∧ hsame comparison (append provenance acceptance) ∧
          PkgSig bundle ledger pkg

theorem CyclotomicRootCarrier_source_triad_obligation [AskSetup] [PackageSetup]
    {numField exponent polynomial splittingField primitiveRoot acceptance comparison provenance
      ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CyclotomicRootCarrier numField exponent polynomial splittingField primitiveRoot acceptance
        comparison provenance ledger bundle pkg ->
      UnaryHistory numField ∧ UnaryHistory splittingField ∧ UnaryHistory primitiveRoot ∧
        UnaryHistory provenance ∧ UnaryHistory acceptance ∧ UnaryHistory ledger ∧
          hsame provenance (append numField splittingField) ∧
            hsame acceptance (append exponent polynomial) ∧
              hsame ledger (append acceptance primitiveRoot) ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have numFieldUnary : UnaryHistory numField := carrier.left
  have exponentUnary : UnaryHistory exponent := carrier.right.left
  have polynomialUnary : UnaryHistory polynomial := carrier.right.right.left
  have splittingFieldUnary : UnaryHistory splittingField := carrier.right.right.right.left
  have primitiveRootUnary : UnaryHistory primitiveRoot := carrier.right.right.right.right.left
  have provenanceCont : Cont numField splittingField provenance :=
    carrier.right.right.right.right.right.left
  have acceptanceCont : Cont exponent polynomial acceptance :=
    carrier.right.right.right.right.right.right.left
  have ledgerCont : Cont acceptance primitiveRoot ledger :=
    carrier.right.right.right.right.right.right.right.left
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed numFieldUnary splittingFieldUnary provenanceCont
  have acceptanceUnary : UnaryHistory acceptance :=
    unary_cont_closed exponentUnary polynomialUnary acceptanceCont
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed acceptanceUnary primitiveRootUnary ledgerCont
  exact And.intro numFieldUnary
    (And.intro splittingFieldUnary
      (And.intro primitiveRootUnary
        (And.intro provenanceUnary
          (And.intro acceptanceUnary
            (And.intro ledgerUnary
              (And.intro provenanceCont
                (And.intro acceptanceCont
                  (And.intro ledgerCont
                    carrier.right.right.right.right.right.right.right.right.right))))))))

end BEDC.Derived.CyclotomicUp
