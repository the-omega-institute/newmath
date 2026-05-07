import BEDC.Derived.PermutationUp
import BEDC.FKernel.NameCert

namespace BEDC.Derived.SymGroupUp

open BEDC.Derived.PermutationUp
open BEDC.FKernel.Ask
open BEDC.FKernel.Bundle
open BEDC.FKernel.Hist
open BEDC.FKernel.NameCert
open BEDC.FKernel.Package
open BEDC.FKernel.Unary

theorem SymGroupCarrier_semantic_name_certificate [AskSetup] [PackageSetup]
    {src tgt graph invGraph comp action ledger : BHist}
    {srcBundle tgtBundle : ProbeBundle ProbeName} {srcPkg tgtPkg : Pkg} :
    PermutationBijectionSourceRow src tgt graph invGraph comp action ledger srcBundle
        tgtBundle srcPkg tgtPkg ->
      SemanticNameCert
          (fun endpoint : BHist => hsame endpoint ledger ∧ UnaryHistory endpoint)
          (fun endpoint : BHist => hsame endpoint ledger ∧ UnaryHistory endpoint)
          (fun endpoint : BHist => hsame endpoint ledger ∧ UnaryHistory endpoint)
          hsame ∧
        (∀ {tail : BHist}, hsame ledger (BHist.e0 tail) -> False) ∧
          (∀ {tail : BHist}, hsame action (BHist.e0 tail) -> False) := by
  intro row
  have surface := PermutationBijectionSourceRow_carrier_surface row
  constructor
  · exact {
      core := {
        carrier_inhabited :=
          Exists.intro ledger (And.intro (hsame_refl ledger) surface.right.right.right.left)
        equiv_refl := by
          intro endpoint _endpointCarrier
          exact hsame_refl endpoint
        equiv_symm := by
          intro _endpoint leftEndpoint same
          exact hsame_symm same
        equiv_trans := by
          intro _endpoint _middle rightEndpoint sameLeft sameRight
          exact hsame_trans sameLeft sameRight
        carrier_respects_equiv := by
          intro endpoint endpoint' sameEndpoint endpointCarrier
          exact And.intro
            (hsame_trans (hsame_symm sameEndpoint) endpointCarrier.left)
            (unary_transport endpointCarrier.right sameEndpoint)
      }
      pattern_sound := by
        intro _endpoint source
        exact source
      ledger_sound := by
        intro _endpoint source
        exact source
    }
  · constructor
    · intro tail sameLedger
      have zeroUnary : UnaryHistory (BHist.e0 tail) :=
        unary_transport surface.right.right.right.left sameLedger
      exact unary_no_zero_extension zeroUnary
    · intro tail sameAction
      have zeroUnary : UnaryHistory (BHist.e0 tail) :=
        unary_transport surface.right.right.left sameAction
      exact unary_no_zero_extension zeroUnary

end BEDC.Derived.SymGroupUp
