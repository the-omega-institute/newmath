import BEDC.Derived.GaloisExtUp

namespace BEDC.Derived.GaloisExtUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary
open BEDC.Derived.SeparableExtUp

theorem GaloisExtSourcePacket_public_interface_export [AskSetup] [PackageSetup]
    {fieldExt polynomial generator minimal simpleRoot sepProvenance separable normality
      separability classifier provenance endpoint action actionLedger fixedBase automorphismSurface :
        BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance separable
        normality separability classifier provenance endpoint bundle pkg ->
      Cont endpoint normality action ->
        Cont action separability actionLedger ->
          Cont fieldExt actionLedger fixedBase ->
            Cont fixedBase classifier automorphismSurface ->
              SemanticNameCert
                (fun target : BHist => exists fixed : BHist,
                  Cont fieldExt actionLedger fixed ∧ Cont fixed classifier target ∧
                    PkgSig bundle endpoint pkg)
                (fun target : BHist => exists fixed : BHist,
                  Cont fieldExt actionLedger fixed ∧ Cont fixed classifier target ∧
                    PkgSig bundle endpoint pkg)
                (fun target : BHist => exists fixed : BHist,
                  Cont fieldExt actionLedger fixed ∧ Cont fixed classifier target ∧
                    PkgSig bundle endpoint pkg)
                (fun left right : BHist =>
                  (exists lf : BHist,
                    Cont fieldExt actionLedger lf ∧ Cont lf classifier left ∧
                      PkgSig bundle endpoint pkg) ∧
                    (exists rf : BHist,
                      Cont fieldExt actionLedger rf ∧ Cont rf classifier right ∧
                        PkgSig bundle endpoint pkg) ∧
                      hsame left right) ∧
                GaloisExtSourcePacket fieldExt polynomial generator minimal simpleRoot sepProvenance
                  separable normality separability classifier provenance endpoint bundle pkg ∧
                  PkgSig bundle endpoint pkg := by
  intro packet actionRow actionLedgerRow fixedBaseRow automorphismSurfaceRow
  have boundary := GaloisExtSourcePacket_public_obligation_boundary packet
  have actionRows :=
    GaloisExtSourcePacket_automorphism_action_source packet actionRow actionLedgerRow
  have endpointPkg : PkgSig bundle endpoint pkg :=
    boundary.right.right.right.right.right.right.right.right.right
  have carrierWitness :
      exists fixed : BHist,
        Cont fieldExt actionLedger fixed ∧ Cont fixed classifier automorphismSurface ∧
          PkgSig bundle endpoint pkg :=
    Exists.intro fixedBase
      (And.intro fixedBaseRow (And.intro automorphismSurfaceRow endpointPkg))
  have cert :
      SemanticNameCert
        (fun target : BHist => exists fixed : BHist,
          Cont fieldExt actionLedger fixed ∧ Cont fixed classifier target ∧
            PkgSig bundle endpoint pkg)
        (fun target : BHist => exists fixed : BHist,
          Cont fieldExt actionLedger fixed ∧ Cont fixed classifier target ∧
            PkgSig bundle endpoint pkg)
        (fun target : BHist => exists fixed : BHist,
          Cont fieldExt actionLedger fixed ∧ Cont fixed classifier target ∧
            PkgSig bundle endpoint pkg)
        (fun left right : BHist =>
          (exists lf : BHist,
            Cont fieldExt actionLedger lf ∧ Cont lf classifier left ∧
              PkgSig bundle endpoint pkg) ∧
            (exists rf : BHist,
              Cont fieldExt actionLedger rf ∧ Cont rf classifier right ∧
                PkgSig bundle endpoint pkg) ∧
              hsame left right) := {
    core := {
      carrier_inhabited := Exists.intro automorphismSurface carrierWitness
      equiv_refl := by
        intro target source
        exact And.intro source (And.intro source (hsame_refl target))
      equiv_symm := by
        intro left right classified
        exact And.intro classified.right.left
          (And.intro classified.left (hsame_symm classified.right.right))
      equiv_trans := by
        intro left middle right leftMiddle middleRight
        exact And.intro leftMiddle.left
          (And.intro middleRight.right.left
            (hsame_trans leftMiddle.right.right middleRight.right.right))
      carrier_respects_equiv := by
        intro left right classified _source
        exact classified.right.left
    }
    pattern_sound := by
      intro target source
      exact source
    ledger_sound := by
      intro target source
      exact source
  }
  have _actionObject :
      UnaryHistory action ∧ UnaryHistory actionLedger ∧ hsame action (append endpoint normality) ∧
        hsame actionLedger (append (append endpoint normality) separability) ∧
          PkgSig bundle endpoint pkg :=
    actionRows
  exact And.intro cert (And.intro packet endpointPkg)

end BEDC.Derived.GaloisExtUp
