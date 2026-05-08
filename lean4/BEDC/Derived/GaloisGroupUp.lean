import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Hist
import BEDC.FKernel.NameCert
import BEDC.FKernel.Package
import BEDC.FKernel.Unary
import BEDC.FKernel.Unary.History

namespace BEDC.Derived.GaloisGroupUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def GaloisGroupAutomorphismActionPacket [AskSetup] [PackageSetup]
    (galois group base action composition inverse classifier provenance ledger : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory galois ∧ UnaryHistory group ∧ UnaryHistory base ∧ UnaryHistory action ∧
    UnaryHistory composition ∧ UnaryHistory inverse ∧ UnaryHistory classifier ∧
      Cont galois group provenance ∧ Cont base action composition ∧
        Cont composition inverse classifier ∧ Cont provenance classifier ledger ∧
          PkgSig bundle ledger pkg

theorem GaloisGroupAutomorphismActionPacket_semantic_name_certificate [AskSetup]
    [PackageSetup]
    {galois group base action composition inverse classifier provenance ledger : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    GaloisGroupAutomorphismActionPacket galois group base action composition inverse
        classifier provenance ledger bundle pkg ->
      SemanticNameCert
        (fun target : BHist =>
          exists carriedClassifier carriedProvenance : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              carriedClassifier carriedProvenance target bundle pkg)
        (fun target : BHist =>
          exists carriedClassifier carriedProvenance : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              carriedClassifier carriedProvenance target bundle pkg)
        (fun target : BHist =>
          exists carriedClassifier carriedProvenance : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              carriedClassifier carriedProvenance target bundle pkg)
        (fun left right : BHist =>
          (exists leftClassifier leftProvenance : BHist,
            GaloisGroupAutomorphismActionPacket galois group base action composition inverse
              leftClassifier leftProvenance left bundle pkg) /\
            (exists rightClassifier rightProvenance : BHist,
              GaloisGroupAutomorphismActionPacket galois group base action composition inverse
                rightClassifier rightProvenance right bundle pkg) /\
              hsame left right) := by
  intro packet
  exact {
    core := {
      carrier_inhabited :=
        Exists.intro ledger (Exists.intro classifier (Exists.intro provenance packet))
      equiv_refl := by
        intro target targetPacket
        exact And.intro targetPacket (And.intro targetPacket (hsame_refl target))
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
        intro left right classified _leftPacket
        exact classified.right.left
    }
    pattern_sound := by
      intro _target source
      exact source
    ledger_sound := by
      intro _target source
      exact source
  }

end BEDC.Derived.GaloisGroupUp
