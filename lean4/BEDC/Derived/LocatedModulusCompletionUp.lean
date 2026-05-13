import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.LocatedModulusCompletionUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def LocatedModulusCompletionCarrier [AskSetup] [PackageSetup]
    (source realSeal modulus limitSeal locatedEvidence transport route provenance localCert
      endpoint : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory source ∧ UnaryHistory realSeal ∧ UnaryHistory modulus ∧
    UnaryHistory limitSeal ∧ UnaryHistory locatedEvidence ∧ UnaryHistory provenance ∧
      Cont source modulus limitSeal ∧ Cont limitSeal realSeal endpoint ∧
        Cont limitSeal locatedEvidence endpoint ∧ Cont endpoint transport route ∧
          Cont route provenance localCert ∧ PkgSig bundle provenance pkg

theorem LocatedModulusCompletionCarrier_namecert_obligations [AskSetup] [PackageSetup]
    {source realSeal modulus limitSeal locatedEvidence transport route provenance localCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedModulusCompletionCarrier source realSeal modulus limitSeal locatedEvidence transport
        route provenance localCert endpoint bundle pkg →
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              LocatedModulusCompletionCarrier source realSeal modulus limitSeal locatedEvidence
                transport route provenance localCert endpoint bundle pkg)
          (fun row : BHist =>
            hsame row endpoint ∧ UnaryHistory source ∧ UnaryHistory modulus ∧
              UnaryHistory limitSeal)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle provenance pkg)
          hsame ∧
        UnaryHistory source ∧ UnaryHistory realSeal ∧ UnaryHistory modulus ∧
          UnaryHistory limitSeal ∧ UnaryHistory locatedEvidence ∧
            Cont source modulus limitSeal ∧ Cont limitSeal realSeal endpoint ∧
              Cont limitSeal locatedEvidence endpoint ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have sourceUnary : UnaryHistory source := carrier.left
  have realSealUnary : UnaryHistory realSeal := carrier.right.left
  have modulusUnary : UnaryHistory modulus := carrier.right.right.left
  have limitSealUnary : UnaryHistory limitSeal := carrier.right.right.right.left
  have locatedEvidenceUnary : UnaryHistory locatedEvidence :=
    carrier.right.right.right.right.left
  have sourceModulusLimit : Cont source modulus limitSeal :=
    carrier.right.right.right.right.right.right.left
  have limitRealEndpoint : Cont limitSeal realSeal endpoint :=
    carrier.right.right.right.right.right.right.right.left
  have limitLocatedEndpoint : Cont limitSeal locatedEvidence endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have sourceAtEndpoint :
      hsame endpoint endpoint ∧
        LocatedModulusCompletionCarrier source realSeal modulus limitSeal locatedEvidence
          transport route provenance localCert endpoint bundle pkg :=
    And.intro (hsame_refl endpoint) carrier
  have cert :
      SemanticNameCert
          (fun row : BHist =>
            hsame row endpoint ∧
              LocatedModulusCompletionCarrier source realSeal modulus limitSeal locatedEvidence
                transport route provenance localCert endpoint bundle pkg)
          (fun row : BHist =>
            hsame row endpoint ∧ UnaryHistory source ∧ UnaryHistory modulus ∧
              UnaryHistory limitSeal)
          (fun row : BHist => hsame row endpoint ∧ PkgSig bundle provenance pkg)
          hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint sourceAtEndpoint
      equiv_refl := by
        intro row _source
        exact hsame_refl row
      equiv_symm := by
        intro row row' sameRows
        exact hsame_symm sameRows
      equiv_trans := by
        intro row row' row'' sameLeft sameRight
        exact hsame_trans sameLeft sameRight
      carrier_respects_equiv := by
        intro row row' sameRows source
        constructor
        · exact hsame_trans (hsame_symm sameRows) source.left
        · exact source.right
    }
    pattern_sound := by
      intro row source
      exact And.intro source.left
        (And.intro sourceUnary (And.intro modulusUnary limitSealUnary))
    ledger_sound := by
      intro row source
      exact And.intro source.left pkgSig
  }
  exact And.intro cert
    (And.intro sourceUnary
      (And.intro realSealUnary
        (And.intro modulusUnary
          (And.intro limitSealUnary
            (And.intro locatedEvidenceUnary
              (And.intro sourceModulusLimit
                (And.intro limitRealEndpoint
                  (And.intro limitLocatedEndpoint pkgSig))))))))

theorem LocatedModulusCompletionCarrier_regular_seal [AskSetup] [PackageSetup]
    {source realSeal modulus limitSeal locatedEvidence transport route provenance localCert
      endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    LocatedModulusCompletionCarrier source realSeal modulus limitSeal locatedEvidence transport
        route provenance localCert endpoint bundle pkg →
      UnaryHistory source ∧ UnaryHistory modulus ∧ UnaryHistory limitSeal ∧
        UnaryHistory endpoint ∧ Cont source modulus limitSeal ∧
          Cont limitSeal realSeal endpoint ∧ Cont limitSeal locatedEvidence endpoint ∧
            PkgSig bundle provenance pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg Cont hsame
  intro carrier
  have sourceUnary : UnaryHistory source := carrier.left
  have realSealUnary : UnaryHistory realSeal := carrier.right.left
  have modulusUnary : UnaryHistory modulus := carrier.right.right.left
  have limitSealUnary : UnaryHistory limitSeal := carrier.right.right.right.left
  have sourceModulusLimit : Cont source modulus limitSeal :=
    carrier.right.right.right.right.right.right.left
  have limitRealEndpoint : Cont limitSeal realSeal endpoint :=
    carrier.right.right.right.right.right.right.right.left
  have limitLocatedEndpoint : Cont limitSeal locatedEvidence endpoint :=
    carrier.right.right.right.right.right.right.right.right.left
  have pkgSig : PkgSig bundle provenance pkg :=
    carrier.right.right.right.right.right.right.right.right.right.right.right
  have endpointUnary : UnaryHistory endpoint :=
    unary_cont_closed limitSealUnary realSealUnary limitRealEndpoint
  exact
    And.intro sourceUnary
      (And.intro modulusUnary
        (And.intro limitSealUnary
          (And.intro endpointUnary
            (And.intro sourceModulusLimit
              (And.intro limitRealEndpoint
                (And.intro limitLocatedEndpoint pkgSig))))))

end BEDC.Derived.LocatedModulusCompletionUp
