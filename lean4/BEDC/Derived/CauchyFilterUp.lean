import BEDC.FKernel.Package
import BEDC.FKernel.Unary

namespace BEDC.Derived.CauchyFilterUp

open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Cont
open BEDC.FKernel.Hist
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

def CauchyFilterPacket [AskSetup] [PackageSetup]
    (stream window threshold endpoint compat transport consumer provenance namecert sealed : BHist)
    (bundle : ProbeBundle ProbeName) (pkg : Pkg) : Prop :=
  UnaryHistory stream ∧ UnaryHistory window ∧ UnaryHistory threshold ∧ UnaryHistory endpoint ∧
    UnaryHistory compat ∧ UnaryHistory transport ∧ UnaryHistory consumer ∧
      UnaryHistory provenance ∧ UnaryHistory namecert ∧ UnaryHistory sealed ∧
        Cont stream window threshold ∧ Cont threshold endpoint compat ∧
          Cont compat transport consumer ∧ Cont consumer provenance namecert ∧
            Cont namecert endpoint sealed ∧ PkgSig bundle sealed pkg

theorem CauchyFilterPacket_refinement_transport [AskSetup] [PackageSetup]
    {stream window threshold endpoint compat transport consumer provenance namecert sealed
      window' threshold' compat' consumer' namecert' sealed' : BHist}
    {bundle : ProbeBundle ProbeName} {pkg : Pkg} :
    CauchyFilterPacket stream window threshold endpoint compat transport consumer provenance
      namecert sealed bundle pkg →
    hsame window window' →
    Cont stream window' threshold' →
    Cont threshold' endpoint compat' →
    Cont compat' transport consumer' →
    Cont consumer' provenance namecert' →
    Cont namecert' endpoint sealed' →
    PkgSig bundle sealed' pkg →
      CauchyFilterPacket stream window' threshold' endpoint compat' transport consumer'
        provenance namecert' sealed' bundle pkg ∧
      hsame threshold threshold' ∧ hsame compat compat' ∧ hsame sealed sealed' := by
  intro packet sameWindow refinedWindow refinedCompat refinedConsumer refinedName refinedSeal refinedPkg
  rcases packet with
    ⟨streamUnary, windowUnary, thresholdUnary, endpointUnary, compatUnary, transportUnary,
      consumerUnary, provenanceUnary, namecertUnary, sealedUnary, originalWindow,
      originalCompat, originalConsumer, originalName, originalSeal, _⟩
  have thresholdSame : hsame threshold threshold' :=
    cont_respects_hsame (hsame_refl stream) sameWindow originalWindow refinedWindow
  have thresholdUnary' : UnaryHistory threshold' :=
    unary_transport thresholdUnary thresholdSame
  have compatSame : hsame compat compat' :=
    cont_respects_hsame thresholdSame (hsame_refl endpoint) originalCompat refinedCompat
  have compatUnary' : UnaryHistory compat' :=
    unary_transport compatUnary compatSame
  have consumerSame : hsame consumer consumer' :=
    cont_respects_hsame compatSame (hsame_refl transport) originalConsumer refinedConsumer
  have consumerUnary' : UnaryHistory consumer' :=
    unary_transport consumerUnary consumerSame
  have namecertSame : hsame namecert namecert' :=
    cont_respects_hsame consumerSame (hsame_refl provenance) originalName refinedName
  have namecertUnary' : UnaryHistory namecert' :=
    unary_transport namecertUnary namecertSame
  have sealedSame : hsame sealed sealed' :=
    cont_respects_hsame namecertSame (hsame_refl endpoint) originalSeal refinedSeal
  have sealedUnary' : UnaryHistory sealed' :=
    unary_transport sealedUnary sealedSame
  have windowUnary' : UnaryHistory window' :=
    unary_transport windowUnary sameWindow
  exact
    And.intro
      (And.intro streamUnary
        (And.intro windowUnary'
          (And.intro thresholdUnary'
            (And.intro endpointUnary
              (And.intro compatUnary'
                (And.intro transportUnary
                  (And.intro consumerUnary'
                    (And.intro provenanceUnary
                      (And.intro namecertUnary'
                        (And.intro sealedUnary'
                          (And.intro refinedWindow
                            (And.intro refinedCompat
                              (And.intro refinedConsumer
                                (And.intro refinedName
                                  (And.intro refinedSeal refinedPkg)))))))))))))))
      (And.intro thresholdSame (And.intro compatSame sealedSame))

end BEDC.Derived.CauchyFilterUp
