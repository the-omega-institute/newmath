import BEDC.Derived.BanachUp
import BEDC.Derived.RingUp
import BEDC.FKernel.Package

namespace BEDC.Derived.CStarAlgUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.BanachUp
open BEDC.Derived.RingUp

def CstaralgebraBHistCarrier [AskSetup] [PackageSetup]
    (banach ring multiplication involution normSquare provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory banach ∧ UnaryHistory ring ∧ UnaryHistory multiplication ∧
    UnaryHistory involution ∧ UnaryHistory normSquare ∧ UnaryHistory provenance ∧
      Cont banach ring multiplication ∧ Cont multiplication involution normSquare ∧
        Cont normSquare provenance ledger ∧ PkgSig bundle ledger pkg

theorem CstaralgebraBHistCarrier_namecert_obligation_surface [AskSetup] [PackageSetup]
    {banach ring multiplication involution normSquare provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CstaralgebraBHistCarrier banach ring multiplication involution normSquare provenance
      ledger bundle pkg ->
      SemanticNameCert (fun row : BHist => hsame row ledger)
        (fun row : BHist => hsame row ledger) (fun row : BHist => hsame row ledger)
        hsame ∧
        UnaryHistory banach ∧ UnaryHistory ring ∧ UnaryHistory multiplication ∧
          UnaryHistory involution ∧ UnaryHistory normSquare ∧ UnaryHistory ledger ∧
            Cont banach ring multiplication ∧ Cont multiplication involution normSquare ∧
              Cont normSquare provenance ledger ∧ PkgSig bundle ledger pkg := by
  intro carrier
  have unaryLedger : UnaryHistory ledger :=
    unary_cont_closed carrier.right.right.right.right.left
      carrier.right.right.right.right.right.left
      carrier.right.right.right.right.right.right.right.right.left
  exact And.intro
    {
      core := {
        carrier_inhabited := Exists.intro ledger (hsame_refl ledger)
        equiv_refl := by
          intro h _source
          exact hsame_refl h
        equiv_symm := by
          intro h k same
          exact hsame_symm same
        equiv_trans := by
          intro h k r sameHK sameKR
          exact hsame_trans sameHK sameKR
        carrier_respects_equiv := by
          intro h k same source
          exact hsame_trans (hsame_symm same) source
      }
      pattern_sound := by
        intro h source
        exact source
      ledger_sound := by
        intro h source
        exact source
    }
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro carrier.right.right.right.right.left
              (And.intro unaryLedger
                (And.intro carrier.right.right.right.right.right.right.left
                  (And.intro carrier.right.right.right.right.right.right.right.left
                    (And.intro carrier.right.right.right.right.right.right.right.right.left
                      carrier.right.right.right.right.right.right.right.right.right)))))))))

def CStarAlgBHistCarrier
    (banach ring involution norm provenance ledger endpoint : BHist) : Prop :=
  BanachSingletonCarrier banach ∧ RingSingletonCarrier ring ∧ UnaryHistory involution ∧
    UnaryHistory norm ∧ UnaryHistory provenance ∧ Cont ring involution ledger ∧
      Cont provenance ledger endpoint

theorem CStarAlgBHistCarrier_namecert_obligation_surface
    {banach ring involution norm provenance ledger endpoint : BHist} :
    CStarAlgBHistCarrier banach ring involution norm provenance ledger endpoint ->
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) hsame ∧
        BanachSingletonCarrier banach ∧ RingSingletonCarrier ring ∧ UnaryHistory involution ∧
          UnaryHistory norm ∧ UnaryHistory ledger ∧ hsame ledger (append ring involution) ∧
            hsame endpoint (append provenance ledger) := by
  intro carrier
  have ledgerUnary : UnaryHistory ledger :=
    unary_cont_closed
      (unary_transport unary_empty (hsame_symm carrier.right.left))
      carrier.right.right.left
      carrier.right.right.right.right.right.left
  have endpointSelf : hsame endpoint endpoint := hsame_refl endpoint
  have cert :
      SemanticNameCert (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint)
          (fun h : BHist => hsame h endpoint) hsame := {
    core := {
      carrier_inhabited := Exists.intro endpoint endpointSelf
      equiv_refl := by
        intro h _source
        exact hsame_refl h
      equiv_symm := by
        intro h k same
        exact hsame_symm same
      equiv_trans := by
        intro h k r sameHK sameKR
        exact hsame_trans sameHK sameKR
      carrier_respects_equiv := by
        intro h k sameHK source
        exact hsame_trans (hsame_symm sameHK) source
    }
    pattern_sound := by
      intro _h source
      exact source
    ledger_sound := by
      intro _h source
      exact source
  }
  exact And.intro cert
    (And.intro carrier.left
      (And.intro carrier.right.left
        (And.intro carrier.right.right.left
          (And.intro carrier.right.right.right.left
            (And.intro ledgerUnary
              (And.intro carrier.right.right.right.right.right.left
                carrier.right.right.right.right.right.right))))))

end BEDC.Derived.CStarAlgUp
