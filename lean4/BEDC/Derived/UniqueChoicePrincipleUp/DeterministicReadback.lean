import BEDC.Derived.UniqueChoicePrincipleUp.TasteGate
import BEDC.FKernel.Ask
import BEDC.FKernel.Bundle
import BEDC.FKernel.Cont
import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.UniqueChoicePrincipleUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def UniqueChoicePrincipleCarrier [AskSetup] [PackageSetup]
    (source relation existence uniqueness deterministic transport replay provenance localName : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont PkgSig hsame
  UnaryHistory source ∧ UnaryHistory relation ∧ UnaryHistory existence ∧
    UnaryHistory uniqueness ∧ UnaryHistory deterministic ∧ UnaryHistory transport ∧
      UnaryHistory replay ∧ UnaryHistory provenance ∧ UnaryHistory localName ∧
        Cont source relation existence ∧ Cont existence uniqueness deterministic ∧
          Cont deterministic transport replay ∧ Cont replay provenance localName ∧
            PkgSig bundle provenance pkg

theorem UniqueChoicePrincipleCarrier_deterministic_readback [AskSetup] [PackageSetup]
    {source relation existence uniqueness deterministic transport replay provenance localName
      leftEvidence rightEvidence leftRead rightRead : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    UniqueChoicePrincipleCarrier source relation existence uniqueness deterministic transport
        replay provenance localName bundle pkg →
      Cont source relation leftEvidence →
        Cont source relation rightEvidence →
          Cont leftEvidence uniqueness leftRead →
            Cont rightEvidence uniqueness rightRead →
              PkgSig bundle leftRead pkg →
                PkgSig bundle rightRead pkg →
                  hsame leftEvidence rightEvidence ∧ hsame leftRead rightRead ∧
                    UnaryHistory leftRead ∧ UnaryHistory rightRead ∧
                      PkgSig bundle provenance pkg ∧ PkgSig bundle leftRead pkg ∧
                        PkgSig bundle rightRead pkg := by
  -- BEDC touchpoint anchor: BHist ProbeBundle Pkg UnaryHistory Cont hsame PkgSig
  intro carrier leftEvidenceRoute rightEvidenceRoute leftReadRoute rightReadRoute leftPkg
    rightPkg
  have sameEvidence : hsame leftEvidence rightEvidence :=
    cont_respects_hsame (hsame_refl source) (hsame_refl relation) leftEvidenceRoute
      rightEvidenceRoute
  have sameRead : hsame leftRead rightRead :=
    cont_respects_hsame sameEvidence (hsame_refl uniqueness) leftReadRoute rightReadRoute
  have leftEvidenceUnary : UnaryHistory leftEvidence :=
    unary_cont_closed carrier.left carrier.right.left leftEvidenceRoute
  have rightEvidenceUnary : UnaryHistory rightEvidence :=
    unary_cont_closed carrier.left carrier.right.left rightEvidenceRoute
  have leftReadUnary : UnaryHistory leftRead :=
    unary_cont_closed leftEvidenceUnary carrier.right.right.right.left leftReadRoute
  have rightReadUnary : UnaryHistory rightRead :=
    unary_cont_closed rightEvidenceUnary carrier.right.right.right.left rightReadRoute
  exact
    ⟨sameEvidence,
      sameRead,
      leftReadUnary,
      rightReadUnary,
      carrier.right.right.right.right.right.right.right.right.right.right.right.right.right,
      leftPkg,
      rightPkg⟩

end BEDC.Derived.UniqueChoicePrincipleUp
