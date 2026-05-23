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

theorem NullSequenceCarrier_window_threshold_exactness [AskSetup] [PackageSetup]
    {difference tolerance window bound sealRow transportRow routes provenance localCert
      toleranceRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NullSequenceCarrier difference tolerance window bound sealRow transportRow routes provenance
        localCert bundle pkg ->
      Cont tolerance window toleranceRead ->
        PkgSig bundle toleranceRead pkg ->
          UnaryHistory difference ∧ UnaryHistory tolerance ∧ UnaryHistory window ∧
            UnaryHistory bound ∧ UnaryHistory sealRow ∧ UnaryHistory toleranceRead ∧
              Cont difference tolerance window ∧ Cont window bound sealRow ∧
                Cont tolerance window toleranceRead ∧ hsame localCert (append provenance sealRow) ∧
                  PkgSig bundle localCert pkg ∧ PkgSig bundle toleranceRead pkg := by
  intro carrier toleranceStep toleranceSig
  obtain ⟨differenceUnary, toleranceUnary, boundUnary, _transportUnary, _routesUnary,
    windowRow, sealRowStep, _provenanceStep, sameLocalCert, localCertSig⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed differenceUnary toleranceUnary windowRow
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed windowUnary boundUnary sealRowStep
  have toleranceReadUnary : UnaryHistory toleranceRead :=
    unary_cont_closed toleranceUnary windowUnary toleranceStep
  exact
    ⟨differenceUnary, toleranceUnary, windowUnary, boundUnary, sealRowUnary,
      toleranceReadUnary, windowRow, sealRowStep, toleranceStep, sameLocalCert, localCertSig,
      toleranceSig⟩

theorem NullSequenceCarrier_non_escape_boundary [AskSetup] [PackageSetup]
    {difference tolerance window bound sealRow transportRow routes provenance localCert sealRead
      realRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    NullSequenceCarrier difference tolerance window bound sealRow transportRow routes provenance
        localCert bundle pkg ->
      Cont window bound sealRead ->
        Cont sealRead provenance realRead ->
          PkgSig bundle realRead pkg ->
            UnaryHistory difference ∧ UnaryHistory tolerance ∧ UnaryHistory window ∧
              UnaryHistory bound ∧ UnaryHistory sealRow ∧ UnaryHistory sealRead ∧
                UnaryHistory realRead ∧ Cont difference tolerance window ∧
                  Cont window bound sealRow ∧ Cont window bound sealRead ∧
                    Cont sealRead provenance realRead ∧ hsame localCert (append provenance sealRow) ∧
                      PkgSig bundle localCert pkg ∧ PkgSig bundle realRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg hsame Cont
  intro carrier sealReadRoute realReadRoute realReadSig
  obtain ⟨differenceUnary, toleranceUnary, boundUnary, transportUnary, routesUnary,
    windowRoute, sealRoute, provenanceRoute, localCertSame, localCertSig⟩ := carrier
  have windowUnary : UnaryHistory window :=
    unary_cont_closed differenceUnary toleranceUnary windowRoute
  have sealRowUnary : UnaryHistory sealRow :=
    unary_cont_closed windowUnary boundUnary sealRoute
  have sealReadUnary : UnaryHistory sealRead :=
    unary_cont_closed windowUnary boundUnary sealReadRoute
  have provenanceUnary : UnaryHistory provenance :=
    unary_cont_closed transportUnary routesUnary provenanceRoute
  have realReadUnary : UnaryHistory realRead :=
    unary_cont_closed sealReadUnary provenanceUnary realReadRoute
  exact
    ⟨differenceUnary, toleranceUnary, windowUnary, boundUnary, sealRowUnary, sealReadUnary,
      realReadUnary, windowRoute, sealRoute, sealReadRoute, realReadRoute, localCertSame,
      localCertSig, realReadSig⟩

end BEDC.Derived.NullSequenceUp
