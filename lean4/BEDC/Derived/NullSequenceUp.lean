import BEDC.FKernel.Bundle
import BEDC.FKernel.Package.Core
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.NullSequenceUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def NullSequenceCarrier [AskSetup] [PackageSetup]
    (difference tolerance window bound sealRow transportRow routes provenance localCert : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory difference ∧ UnaryHistory tolerance ∧ UnaryHistory bound ∧
    UnaryHistory transportRow ∧ UnaryHistory routes ∧ Cont difference tolerance window ∧
      Cont window bound sealRow ∧ Cont transportRow routes provenance ∧
        hsame localCert (append provenance sealRow) ∧ PkgSig bundle localCert pkg

theorem NullSequenceCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {difference tolerance window bound sealRow transportRow routes provenance localCert : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NullSequenceCarrier difference tolerance window bound sealRow transportRow routes provenance
        localCert bundle pkg ->
      UnaryHistory difference ∧ UnaryHistory tolerance ∧ UnaryHistory window ∧
        UnaryHistory bound ∧ UnaryHistory sealRow ∧ UnaryHistory transportRow ∧
          UnaryHistory routes ∧ UnaryHistory provenance ∧ UnaryHistory localCert ∧
            Cont difference tolerance window ∧ Cont window bound sealRow ∧
              Cont transportRow routes provenance ∧ hsame localCert (append provenance sealRow) ∧
                PkgSig bundle localCert pkg := by
  intro carrier
  have differenceUnary : UnaryHistory difference := carrier.left
  have toleranceUnary : UnaryHistory tolerance := carrier.right.left
  have boundUnary : UnaryHistory bound := carrier.right.right.left
  have transportUnary : UnaryHistory transportRow := carrier.right.right.right.left
  have routesUnary : UnaryHistory routes := carrier.right.right.right.right.left
  have windowRow : Cont difference tolerance window :=
    carrier.right.right.right.right.right.left
  have sealCont : Cont window bound sealRow :=
    carrier.right.right.right.right.right.right.left
  have provenanceRow : Cont transportRow routes provenance :=
    carrier.right.right.right.right.right.right.right.left
  have sameLocalCert : hsame localCert (append provenance sealRow) :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgRow : PkgSig bundle localCert pkg :=
    carrier.right.right.right.right.right.right.right.right.right
  have windowUnary : UnaryHistory window :=
    unary_cont_closed differenceUnary toleranceUnary windowRow
  have sealUnary : UnaryHistory sealRow :=
    unary_cont_closed windowUnary boundUnary sealCont
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary routesUnary provenanceRow
  have localCertUnary : UnaryHistory localCert :=
    unary_transport (unary_append_closed provenanceUnary sealUnary) (hsame_symm sameLocalCert)
  exact And.intro differenceUnary
    (And.intro toleranceUnary
      (And.intro windowUnary
        (And.intro boundUnary
          (And.intro sealUnary
            (And.intro transportUnary
              (And.intro routesUnary
                (And.intro provenanceUnary
                  (And.intro localCertUnary
                    (And.intro windowRow
                      (And.intro sealCont
                        (And.intro provenanceRow (And.intro sameLocalCert pkgRow))))))))))))

end BEDC.Derived.NullSequenceUp
