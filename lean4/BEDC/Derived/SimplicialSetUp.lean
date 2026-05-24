import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary.History
import BEDC.Derived.SimplicialSetUp.TasteGate

namespace BEDC.Derived.SimplicialSetUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def SimplicialSetBHistSimplexRowCarrier [AskSetup] [PackageSetup]
    (functor simplex face degeneracy package provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  Cont functor simplex face ∧ Cont simplex functor degeneracy ∧
    PkgSig bundle provenance pkg ∧ Cont package provenance ledger

theorem SimplicialSetBHistSimplexRowCarrier_namecert_obligation_surface
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      SemanticNameCert
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun left right : BHist =>
            (exists lf ld lp ll : BHist,
              SimplicialSetBHistSimplexRowCarrier functor left lf ld lp provenance ll
                bundle pkg) ∧
            (exists rf rd rp rl : BHist,
              SimplicialSetBHistSimplexRowCarrier functor right rf rd rp provenance rl
                bundle pkg) ∧
              hsame left right) ∧
        Cont functor simplex face ∧ Cont simplex functor degeneracy ∧
          PkgSig bundle provenance pkg := by
  intro carrier
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          refine Exists.intro simplex ?_
          refine Exists.intro face ?_
          refine Exists.intro degeneracy ?_
          refine Exists.intro package ?_
          exact Exists.intro ledger carrier
        equiv_refl := by
          intro endpoint source
          exact And.intro source (And.intro source (hsame_refl endpoint))
        equiv_symm := by
          intro left right same
          exact And.intro same.right.left
            (And.intro same.left (hsame_symm same.right.right))
        equiv_trans := by
          intro left middle right sameLeftMiddle sameMiddleRight
          exact And.intro sameLeftMiddle.left
            (And.intro sameMiddleRight.right.left
              (hsame_trans sameLeftMiddle.right.right sameMiddleRight.right.right))
        carrier_respects_equiv := by
          intro left right same _source
          exact same.right.left
      }
      pattern_sound := by
        intro endpoint source
        exact source
      ledger_sound := by
        intro endpoint source
        exact source
    }
  · exact And.intro carrier.left (And.intro carrier.right.left carrier.right.right.left)

theorem SimplicialSetBHistSimplexRowCarrier_functor_source_boundary
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      Cont functor simplex face ∧ Cont simplex functor degeneracy ∧
        PkgSig bundle provenance pkg ∧ hsame face (append functor simplex) ∧
          hsame degeneracy (append simplex functor) := by
  intro carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.left
        (And.intro carrier.left carrier.right.left)))

theorem SimplicialSetBHistSimplexRowCarrier_simplicial_identity_ledger_coverage
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      Cont functor simplex face ∧ Cont simplex functor degeneracy ∧
        Cont package provenance ledger ∧ PkgSig bundle provenance pkg ∧
          hsame face (append functor simplex) ∧ hsame degeneracy (append simplex functor) ∧
            hsame ledger (append package provenance) := by
  intro carrier
  exact And.intro carrier.left
    (And.intro carrier.right.left
      (And.intro carrier.right.right.right
        (And.intro carrier.right.right.left
          (And.intro carrier.left
            (And.intro carrier.right.left carrier.right.right.right)))))

theorem SimplicialSetBHistSimplexRowCarrier_face_degeneracy_endpoint_coverage
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      Cont face degeneracy endpoint ->
        hsame endpoint (append face degeneracy) ∧ Cont functor simplex face ∧
          Cont simplex functor degeneracy ∧ Cont package provenance ledger ∧
            PkgSig bundle provenance pkg := by
  intro carrier endpointRow
  exact And.intro endpointRow
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.right carrier.right.right.left)))

theorem SimplicialSetBHistSimplexRowCarrier_public_dependency_scope
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      SemanticNameCert
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun endpoint : BHist =>
            exists face degeneracy package ledger : BHist,
              SimplicialSetBHistSimplexRowCarrier functor endpoint face degeneracy package
                provenance ledger bundle pkg)
          (fun left right : BHist =>
            (exists lf ld lp ll : BHist,
              SimplicialSetBHistSimplexRowCarrier functor left lf ld lp provenance ll
                bundle pkg) ∧
            (exists rf rd rp rl : BHist,
              SimplicialSetBHistSimplexRowCarrier functor right rf rd rp provenance rl
                bundle pkg) ∧
              hsame left right) ∧
        Cont functor simplex face ∧ Cont simplex functor degeneracy ∧
          Cont package provenance ledger ∧ PkgSig bundle provenance pkg := by
  intro carrier
  have obligation :=
    SimplicialSetBHistSimplexRowCarrier_namecert_obligation_surface carrier
  have ledger :=
    SimplicialSetBHistSimplexRowCarrier_simplicial_identity_ledger_coverage carrier
  exact And.intro obligation.left
    (And.intro ledger.left
      (And.intro ledger.right.left
        (And.intro ledger.right.right.left ledger.right.right.right.left)))

theorem SimplicialSetBHistSimplexRowCarrier_face_endpoint_scope_binding
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger endpoint : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      Cont face degeneracy endpoint ->
        SemanticNameCert
            (fun row : BHist => hsame row endpoint ∧ Cont functor simplex face ∧
              Cont simplex functor degeneracy ∧ Cont face degeneracy endpoint ∧
                Cont package provenance ledger ∧ PkgSig bundle provenance pkg)
            (fun row : BHist => hsame row endpoint ∧ Cont functor simplex face ∧
              Cont simplex functor degeneracy ∧ Cont face degeneracy endpoint ∧
                Cont package provenance ledger ∧ PkgSig bundle provenance pkg)
            (fun row : BHist => hsame row endpoint ∧ Cont functor simplex face ∧
              Cont simplex functor degeneracy ∧ Cont face degeneracy endpoint ∧
                Cont package provenance ledger ∧ PkgSig bundle provenance pkg)
            hsame ∧ hsame endpoint (append face degeneracy) := by
  intro carrier endpointRow
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact Exists.intro endpoint
            (And.intro (hsame_refl endpoint)
              (And.intro carrier.left
                (And.intro carrier.right.left
                  (And.intro endpointRow
                    (And.intro carrier.right.right.right carrier.right.right.left)))))
        equiv_refl := by intro row _rowCarrier; exact hsame_refl row
        equiv_symm := by intro _left _right same; exact hsame_symm same
        equiv_trans := by intro _left _middle _right sameLM sameMR; exact hsame_trans sameLM sameMR
        carrier_respects_equiv := by
          intro left right same source
          exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
      }
      pattern_sound := by intro _row source; exact source
      ledger_sound := by intro _row source; exact source
    }
  · exact endpointRow

theorem SimplicialSetBHistSimplexRowCarrier_identity_ledger_scope_binding
    [AskSetup] [PackageSetup]
    {functor simplex face degeneracy package provenance ledger endpoint identityLedger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    SimplicialSetBHistSimplexRowCarrier functor simplex face degeneracy package provenance
        ledger bundle pkg ->
      UnaryHistory ledger ->
        UnaryHistory endpoint ->
          Cont face degeneracy endpoint ->
            Cont ledger endpoint identityLedger ->
              SemanticNameCert
                  (fun row : BHist =>
                    hsame row identityLedger ∧ Cont functor simplex face ∧
                      Cont simplex functor degeneracy ∧ Cont face degeneracy endpoint ∧
                        Cont package provenance ledger ∧
                          Cont ledger endpoint identityLedger ∧ PkgSig bundle provenance pkg)
                  (fun row : BHist =>
                    hsame row identityLedger ∧ Cont functor simplex face ∧
                      Cont simplex functor degeneracy ∧ Cont face degeneracy endpoint ∧
                        Cont package provenance ledger ∧
                          Cont ledger endpoint identityLedger ∧ PkgSig bundle provenance pkg)
                  (fun row : BHist =>
                    hsame row identityLedger ∧ Cont functor simplex face ∧
                      Cont simplex functor degeneracy ∧ Cont face degeneracy endpoint ∧
                        Cont package provenance ledger ∧
                          Cont ledger endpoint identityLedger ∧ PkgSig bundle provenance pkg)
                  hsame ∧ UnaryHistory identityLedger ∧
                hsame identityLedger (append ledger endpoint) := by
  intro carrier ledgerUnary endpointUnary endpointRow identityLedgerRow
  have identityLedgerUnary : UnaryHistory identityLedger :=
    unary_cont_closed ledgerUnary endpointUnary identityLedgerRow
  constructor
  · exact {
      core := {
        carrier_inhabited := by
          exact Exists.intro identityLedger
            (And.intro (hsame_refl identityLedger)
              (And.intro carrier.left
                (And.intro carrier.right.left
                  (And.intro endpointRow
                    (And.intro carrier.right.right.right
                      (And.intro identityLedgerRow carrier.right.right.left))))))
        equiv_refl := by intro row _rowCarrier; exact hsame_refl row
        equiv_symm := by intro _left _right same; exact hsame_symm same
        equiv_trans := by intro _left _middle _right sameLM sameMR; exact hsame_trans sameLM sameMR
        carrier_respects_equiv := by
          intro left right same source
          exact And.intro (hsame_trans (hsame_symm same) source.left) source.right
      }
      pattern_sound := by intro _row source; exact source
      ledger_sound := by intro _row source; exact source
    }
  · exact And.intro identityLedgerUnary identityLedgerRow

def SimplicialSetSimplexRowCarrier
    (functor finite endpoint package route : BHist) : Prop :=
  UnaryHistory functor ∧ UnaryHistory finite ∧ UnaryHistory package ∧
    Cont functor finite endpoint ∧ Cont endpoint package route

def SimplicialSetFaceDegeneracyClassifier
    (functor finite endpoint package route functor' finite' endpoint' package' route' : BHist) :
    Prop :=
  hsame functor functor' ∧ hsame finite finite' ∧ hsame endpoint endpoint' ∧
    hsame package package' ∧ hsame route route'

theorem SimplicialSetFaceDegeneracyClassifier_ledger_stability
    {functor functor' finite finite' endpoint endpoint' package package' route route' :
      BHist} :
    SimplicialSetSimplexRowCarrier functor finite endpoint package route ->
      SimplicialSetSimplexRowCarrier functor' finite' endpoint' package' route' ->
        hsame functor functor' ->
          hsame finite finite' ->
            hsame package package' ->
              SimplicialSetFaceDegeneracyClassifier functor finite endpoint package route
                  functor' finite' endpoint' package' route' ∧
                hsame endpoint endpoint' ∧ hsame route route' := by
  intro carrier carrier' sameFunctor sameFinite samePackage
  have sameEndpoint : hsame endpoint endpoint' :=
    cont_respects_hsame sameFunctor sameFinite carrier.right.right.right.left
      carrier'.right.right.right.left
  have sameRoute : hsame route route' :=
    cont_respects_hsame sameEndpoint samePackage carrier.right.right.right.right
      carrier'.right.right.right.right
  exact And.intro
    (And.intro sameFunctor
      (And.intro sameFinite
        (And.intro sameEndpoint (And.intro samePackage sameRoute))))
    (And.intro sameEndpoint sameRoute)

end BEDC.Derived.SimplicialSetUp
